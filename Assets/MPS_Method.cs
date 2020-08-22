using System;
using System.Collections;
using System.Collections.Generic;
using UnityEngine;

public class MPS_Method : MonoBehaviour
{
    //モデル粒子の情報を呼び出す
    public GameObject particle;
    public GameObject particle_wall;

    //水の密度(kg/m^3)を保存するリスト(5~30℃)
    public static float[] densities = new float[26] { 999.993f, 999.974f, 999.938f, 999.987f, 999.887f, 999.821f, 999.741f, 999.647f, 999.539f, 999.418f, 999.284f, 999.138f, 998.980f, 998.628f, 998.436f, 998.223f, 998.019f, 997.794f, 997.560f, 997.316f, 997.062f, 996.799f, 996.526f, 996.244f, 995.954f, 995.654f };

    //水の粘度(Pa・s)を保存するリスト(5~30℃)
    public static float[] viscosities = new float[26] { 1518.94f, 1472.21f, 1427.74f, 1385.39f, 1345.02f, 1306.51f, 1269.74f, 1234.61f, 1201.02f, 1168.87f, 1138.09f, 1108.59f, 1080.30f, 1053.16f, 1027.11f, 1002.07f, 978.01f, 954.86f, 932.59f, 911.15f, 890.49f, 870.57f, 851.37f, 832.85f, 814.96f, 797.70f };

    //水温を標準入力から受け取る(5~30℃)
    public int temperature;

    //影響半径を標準入力から受け取る
    public float r_e;

    //位置を保存するリスト,速度を保存するリスト,粒子数密度を保存するリストの定義
    public static List<Vector3> position_l = new List<Vector3>();
    public static List<Vector3> velocity_l = new List<Vector3>();
    public static List<float> n_l = new List<float>();

    //流体を表す粒子数の数
    public static int cnt = 0;
    //床を表す粒子の数
    public static int add_cnt = 0;

    //λ
    public static float lambda = 0f;

    //粒子数密度の初期値
    public static float n0 = 0f;

    //自由表面粒子の判別式に使うalpha
    public static float alpha = 0.95f;

    public static int roop_cnt = 0;

    //重み関数
    float W(float xi, float yi, float zi, float xj, float yj, float zj)
    {
        float r = distance(xi, yi, zi, xj, yj, zj);
        if (r_e < r) return 0f;
        return r_e / r - 1;
    }

    //二乗を計算する関数
    float Pow2(float x)
    {
        return x * x;
    }

    //内積を計算する関数
    float dot(float[] a, float[] b, int n)
    {
        float ans = 0;
        for (int i = 0; i < n; i++)
        {
            ans += a[i] * b[i];
        }
        return (ans);
    }

    //2点間の距離を求める関数
    float distance(float xi, float yi, float zi, float xj, float yj, float zj)
    {
        return (float)Math.Sqrt(Pow2(xj - xi) + Pow2(yj - yi) + Pow2(zj - zi));
    }

    //不完全コレスキー分解
    //正定値対称行列Aを、対角要素が1の下三角行列と対角行列の積に(LDL^T)分解する
    int IncompleteCholeskyDecomp(float[][] A, float[,] L, float[] d, int n)
    {
        if (n <= 0) return 0;

        L[0, 0] = A[0][0];
        d[0] = 1.0f / L[0, 0];
        //Debug.Log(A[0][0] + " " + d[0]);
        for (int i = 1; i < n; i++)
        {
            for (int j = 0; j <= i; j++)
            {
                if (Math.Abs(A[i][j]) < 1.0e-10) continue;

                float lld = A[i][j];
                for (int k = 0; k < j; k++)
                {
                    lld -= L[i, k] * L[j, k] * d[k];
                }
                L[i, j] = lld;
                //Debug.Log(lld + " " + i + " " + j);
            }
            d[i] = 1.0f / L[i, i];
            //Debug.Log(d[i] + " " + i);
        }
        return 1;
    }

    //前進代入、後進代入で(LDL^T)^-1rを計算する関数
    void ICRes(float[,] L, float[] d, float[] r, float[] u, int n)
    {
        float[] y = new float[n];
        for (int i = 0; i < n; i++)
        {
            float rly = r[i];
            for (int j = 0; j < i; j++)
            {
                rly -= L[i, j] * y[j];
            }
            y[i] = rly / L[i, i];
        }
        for (int i = n - 1; i >= 0; i--)
        {
            float lu = 0f;
            for (int j = i + 1; j < n; j++)
            {
                lu += L[i, j] * u[j];
            }
            u[i] = y[i] - d[i] * lu;
        }
    }

    //不完全コレスキー分解付き共役勾配法
    int ICCGSolver(float[][] A, float[] b, float[] x, int n, int max_iter, float eps)
    {
        if (n <= 0) return 0;
        //使用する変数の定義
        float[] r = new float[n];
        float[] p = new float[n];
        float[] y = new float[n];
        float[] r2 = new float[n];
        float[] d = new float[n];
        float[,] L = new float[n, n];
        //不完全コレスキー分解
        IncompleteCholeskyDecomp(A, L, d, n);
        //第0近似解に対する残差の計算
        for (int i = 0; i < n; i++)
        {
            float ax = 0f;
            for (int j = 0; j < n; j++)
            {
                ax += A[i][j] * x[j];
            }
            r[i] = b[i] - ax;
        }
        //p_0 = (LDL^T)^-1 r_0の計算
        ICRes(L, d, r, p, n);
        float rr0 = dot(r, p, n);
        float rr1, alpha, beta;
        float e = 0;
        int k;
        for (k = 0; k < max_iter; k++)
        {
            //y=APの計算
            for (int i = 0; i < n; i++)
            {

                y[i] = dot(A[i], p, n);
            }
            //alpha=rr0/(P*AP)の計算
            alpha = rr0 / dot(p, y, n);
            //解x、残差rの更新
            for (int i = 0; i < n; i++)
            {
                x[i] += alpha * p[i];
                r[i] -= alpha * y[i];
            }
            //(r*r)_(k+1)の計算
            ICRes(L, d, r, r2, n);
            rr1 = dot(r, r2, n);
            //収束判定(||r||<=eps)
            e = (float)Math.Sqrt(rr1);
            if (e < eps)
            {
                k++;
                break;
            }
            //βの計算とPの更新
            beta = rr1 / rr0;
            for (int i = 0; i < n; i++)
            {
                p[i] = r2[i] + beta * p[i];
            }
            //(r*r)_(k+1)を次のステップのために確保しておく
            rr0 = rr1;
        }
        max_iter = k;
        eps = e;
        return 1;
    }

    //最初一回だけ呼び出される関数
    void Start()
    {
        //等間隔で粒子を配置していく(隙間はなし、体心立方格子みたいな感じ)
        //(x,y,z)で粒子の中心座標を示す
        //半径0.05f
        //xの範囲
        for (var x = -2; x < 3; x++)
        {
            //yの範囲
            for (var y = 0; y < 4; y++)
            {
                //zの範囲
                for (var z = -2; z < 3; z++)
                {
                    //モデル粒子を(x,y,z)の点に回転なしで作成
                    Instantiate(particle, new Vector3(0.1f * x, 0.1f * y, 0.1f * z), Quaternion.identity);

                    particle.transform.parent = this.transform;

                    //それぞれのリストの初期化
                    position_l.Add(new Vector3(0.1f * x, 0.1f * y, 0.1f * z));
                    velocity_l.Add(new Vector3(0f, 0f, 0f));
                    n_l.Add(0);

                    //粒子数のカウント
                    cnt++;
                }
            }
        }

        /*
        for (var x = -4; x < -2; x++)
        {
            for (var y = 0; y < 4; y++)
            {
                for (var z = -4; z < 5; z++)
                {
                    Instantiate(particle_wall, new Vector3(0.1f * x, 0.1f * y, 0.1f * z), Quaternion.identity);

                    //床粒子のもきちんと加えておこう
                    position_l.Add(new Vector3(0.1f * x, 0.1f * y, 0.1f * z));
                    velocity_l.Add(new Vector3(0f, 0f, 0f));
                    n_l.Add(0);

                    //粒子数のカウント
                    add_cnt++;
                }
            }
        }
        
        for (var x = 3; x < 5; x++)
        {
            for (var y = 0; y < 4; y++)
            {
                for (var z = -4; z < 5; z++)
                {
                    Instantiate(particle_wall, new Vector3(0.1f * x, 0.1f * y, 0.1f * z), Quaternion.identity);

                    //床粒子のもきちんと加えておこう
                    position_l.Add(new Vector3(0.1f * x, 0.1f * y, 0.1f * z));
                    velocity_l.Add(new Vector3(0f, 0f, 0f));
                    n_l.Add(0);

                    //粒子数のカウント
                    add_cnt++;
                }
            }
        }
        for (var x = -2; x < 3; x++)
        {
            for (var y = 0; y < 4; y++)
            {
                for (var z = -4; z < -2; z++)
                {
                    Instantiate(particle_wall, new Vector3(0.1f * x, 0.1f * y, 0.1f * z), Quaternion.identity);

                    //床粒子のもきちんと加えておこう
                    position_l.Add(new Vector3(0.1f * x, 0.1f * y, 0.1f * z));
                    velocity_l.Add(new Vector3(0f, 0f, 0f));
                    n_l.Add(0);

                    //粒子数のカウント
                    add_cnt++;
                }
            }
        }
        for (var x = -2; x < 3; x++)
        {
            for (var y = 0; y < 4; y++)
            {
                for (var z = 3; z < -5; z++)
                {
                    Instantiate(particle_wall, new Vector3(0.1f * x, 0.1f * y, 0.1f * z), Quaternion.identity);

                    //床粒子のもきちんと加えておこう
                    position_l.Add(new Vector3(0.1f * x, 0.1f * y, 0.1f * z));
                    velocity_l.Add(new Vector3(0f, 0f, 0f));
                    n_l.Add(0);

                    //粒子数のカウント
                    add_cnt++;
                }
            }
        }
        */

        //粒子で床を作ろう
        //等間隔で平たく作っていく
        //厚さは影響半径よりも大きくなるようにする
        //上と同様の考え方で
        for (var x = -4; x < 5; x++)
        {
            for (var y = -2; y < 0; y++)
            {
                for (var z = -4; z < 5; z++)
                {
                    Instantiate(particle_wall, new Vector3(0.1f * x, 0.1f * y, 0.1f * z), Quaternion.identity);

                    //床粒子のもきちんと加えておこう
                    position_l.Add(new Vector3(0.1f * x, 0.1f * y, 0.1f * z));
                    velocity_l.Add(new Vector3(0f, 0f, 0f));
                    n_l.Add(0);

                    //粒子数のカウント
                    add_cnt++;
                }
            }
        }


        //λは使いまわせるからここで計算してしまおう
        //λを表す分数の分子の定義(λ=n/d)、d=n0
        float n = 0f;

        //Σi≠j(i=52)
        float xi_x = position_l[52].x;
        float xi_y = position_l[52].y;
        float xi_z = position_l[52].z;
        for (int j = 0; j < cnt; j++)
        {
            //粒子xjの座標の取得
            if (52 == j) continue;
            float xj_x = position_l[j].x;
            float xj_y = position_l[j].y;
            float xj_z = position_l[j].z;

            //n0(λの分母d)に関する計算
            n0 += W(xi_x, xi_y, xi_z, xj_x, xj_y, xj_z);

            //λに関する計算
            //分子nについての計算
            n += (Pow2(xj_x - xi_x) + Pow2(xj_y - xi_y) + Pow2(xj_z - xi_z)) * W(xi_x, xi_y, xi_z, xj_x, xj_y, xj_z);

        }
        //λの算出
        lambda = n / n0;
    }

    //物理演算
    //0.02秒毎に呼び出す
    void FixedUpdate()
    {
        roop_cnt++;
        //密度と粘度の取得
        float density = densities[temperature - 5];
        float viscosity = viscosities[temperature - 5];

        //各粒子に対して計算
        for (int i = 0; i < cnt + add_cnt; i++)
        {
            //粘性項を離散化したときに出てくるΣ
            //各軸ごとに計算するので3つ
            float sigma_x = 0f;
            float sigma_y = 0f;
            float sigma_z = 0f;

            //粒子xiの座標の取得
            float xi_x = position_l[i].x;
            float xi_y = position_l[i].y;
            float xi_z = position_l[i].z;

            //粒子xiの速度の取得
            float xi_vx = velocity_l[i].x;
            float xi_vy = velocity_l[i].y;
            float xi_vz = velocity_l[i].z;

            //Σi≠j
            for (int j = 0; j < cnt + add_cnt; j++)
            {
                //粒子xjの座標の取得
                if (i == j) continue;
                float xj_x = position_l[j].x;
                float xj_y = position_l[j].y;
                float xj_z = position_l[j].z;

                //粒子xjの速度の取得
                float xj_vx = velocity_l[j].x;
                float xj_vy = velocity_l[j].y;
                float xj_vz = velocity_l[j].z;

                //Σの計算
                sigma_x += (xj_vx - xi_vx) * W(xi_x, xi_y, xi_z, xj_x, xj_y, xj_z);
                sigma_y += (xj_vy - xi_vy) * W(xi_x, xi_y, xi_z, xj_x, xj_y, xj_z);
                sigma_z += (xj_vz - xi_vz) * W(xi_x, xi_y, xi_z, xj_x, xj_y, xj_z);
            }

            //粘性項の算出(d = 3)
            float viscosity_x = 2 * 3 * sigma_x / lambda / n0;
            float viscosity_y = 2 * 3 * sigma_y / lambda / n0;
            float viscosity_z = 2 * 3 * sigma_z / lambda / n0;

            if (i >= cnt) continue;

            //速度と位置の更新(仮)
            //漸化式に倣って更新していく(Δt = 0.02, g = -9.81)
            //速度の更新(仮)
            float vx_temporary = velocity_l[i].x + 0.02f * (viscosity * viscosity_x / density);
            float vy_temporary = velocity_l[i].y + 0.02f * (viscosity * viscosity_y / density - 9.81f);
            float vz_temporary = velocity_l[i].z + 0.02f * (viscosity * viscosity_z / density);
            velocity_l[i] = new Vector3(vx_temporary, vy_temporary, viscosity_z);

            //位置の更新(仮)
            float x_temporary = position_l[i].x + 0.02f * vx_temporary;
            float y_temporary = position_l[i].y + 0.02f * vy_temporary;
            float z_temporary = position_l[i].z + 0.02f * vz_temporary;
            position_l[i] = new Vector3(x_temporary, y_temporary, z_temporary);
        }

        //仮位置における粒子数密度nの算出
        //各粒子に対して計算
        for (int i = 0; i < cnt + add_cnt; i++)
        {
            //仮位置における粒子数密度n
            float n = 0f;

            //粒子xiの座標の取得
            float xi_x = position_l[i].x;
            float xi_y = position_l[i].y;
            float xi_z = position_l[i].z;

            //Σi≠j
            for (int j = 0; j < cnt + add_cnt; j++)
            {
                //粒子xjの座標の取得
                if (i == j) continue;
                float xj_x = position_l[j].x;
                float xj_y = position_l[j].y;
                float xj_z = position_l[j].z;

                //nに関する計算
                n += W(xi_x, xi_y, xi_z, xj_x, xj_y, xj_z);
            }
            //計算結果をリストに保存
            n_l[i] = n;
        }

        //行列のサイズ
        int A_size = 0;
        for (int i = 0; i < cnt + add_cnt; i++)
        {
            //ディリクレ境界条件
            if (n_l[i] < alpha * n0) continue;
            A_size++;
        }

        //圧力pについてのポアソン方程式を解く
        //係数行列Aの定義(ジャグ配列)
        float[][] A = new float[A_size][];
        int xi = 0;
        for (int i = 0; i < cnt + add_cnt; i++)
        {
            //ディリクレ境界条件
            if (n_l[i] < alpha * n0) continue;

            //粒子xiの座標の取得
            float xi_x = position_l[i].x;
            float xi_y = position_l[i].y;
            float xi_z = position_l[i].z;

            //係数行列の初期化
            A[xi] = new float[A_size];
            int xj = 0;
            for (int j = 0; j < cnt + add_cnt; j++)
            {
                //粒子xjの座標の取得
                float xj_x = position_l[j].x;
                float xj_y = position_l[j].y;
                float xj_z = position_l[j].z;

                //Σi≠j
                if (i == j)
                {
                    xj++;
                    continue;
                }

                A[xi][xi] -= W(xi_x, xi_y, xi_z, xj_x, xj_y, xj_z);

                //ディリクレ境界条件
                if (n_l[j] < alpha * n0) continue;
                else
                {
                    A[xi][xj] = W(xi_x, xi_y, xi_z, xj_x, xj_y, xj_z);
                    //列のindexの更新
                    xj++;
                }
            }
            //行のindexを更新
            xi++;
        }

        //デバッグ用
        /*
        for (int i = 0; i < A_size; i++)
        {
            for (int j = 0; j < A_size; j++)
            {
                Debug.Log(A[i][j] + " " + i + " " + j);
            }
        }
        //*/

        //結果ベクトルの定義
        float[] pressure_l = new float[A_size];

        //右辺ベクトルの定義
        float[] b = new float[A_size];
        xi = 0;
        for (int i = 0; i < cnt + add_cnt; i++)
        {
            //ディリクレ境界条件
            float alpha = 0.95f;
            if (n_l[i] < alpha * n0) continue;

            //Δt=0.02、d=3で計算
            b[xi] = density * lambda * n0 * (n0 - n_l[i]) / (6 * 0.02f * 0.02f * n_l[i]);
            //Debug.Log(b[xi]);
            xi++;
        }

        //不完全コレスキー分解付き共役勾配法を用いてこの方程式を解く
        ICCGSolver(A, b, pressure_l, A_size, 10000, 0.001f);

        //デバッグ用
        /*
        for (int i = 0; i < A_size; i++)
        {
            Debug.Log(pressure_l[i]);
        }
        //*/

        //求めた圧力から正しい速度と位置を得る
        //各粒子について更新
        xi = 0;
        for (int i = 0; i < cnt; i++)
        {
            //ディリクレ境界条件
            float alpha = 0.95f;
            float xi_p;
            if (n_l[i] < alpha * n0)
            {
                xi_p = 0;
            }
            else
            {
                xi_p = pressure_l[xi];
                xi++;
            }

            //粒子xiの座標の取得
            float xi_x = position_l[i].x;
            float xi_y = position_l[i].y;
            float xi_z = position_l[i].z;

            //∇piを求める
            float np_x = 0;
            float np_y = 0;
            float np_z = 0;

            //Σi≠j
            int xj = 0;
            for (int j = 0; j < cnt + add_cnt; j++)
            {
                //粒子xjの座標の取得
                if (i == j) continue;
                float xj_x = position_l[j].x;
                float xj_y = position_l[j].y;
                float xj_z = position_l[j].z;

                //ディリクレ境界条件
                float xj_p;
                if (n_l[j] < alpha * n0)
                {
                    xj_p = 0;
                }
                else
                {
                    xj_p = pressure_l[xj];
                    xj++;
                }

                //圧力の勾配ベクトル
                np_x += (xj_p - xi_p) * (xj_x - xi_x) * W(xi_x, xi_y, xi_z, xj_x, xj_y, xj_z) / (Pow2(xj_x - xi_x) + Pow2(xj_y - xi_y) + Pow2(xj_z - xi_z));
                np_y += (xj_p - xi_p) * (xj_y - xi_y) * W(xi_x, xi_y, xi_z, xj_x, xj_y, xj_z) / (Pow2(xj_x - xi_x) + Pow2(xj_y - xi_y) + Pow2(xj_z - xi_z));
                np_z += (xj_p - xi_p) * (xj_z - xi_z) * W(xi_x, xi_y, xi_z, xj_x, xj_y, xj_z) / (Pow2(xj_x - xi_x) + Pow2(xj_y - xi_y) + Pow2(xj_z - xi_z));
            }
            //d=3で計算
            np_x = np_x * 3 / n0;
            np_y = np_y * 3 / n0;
            np_z = np_z * 3 / n0;

            //速度の更新
            float vx = 0;
            float vy = 0;
            float vz = 0;
            //Δt=0.02で計算
            vx = velocity_l[i].x - 0.02f * np_x / density;
            vy = velocity_l[i].y - 0.02f * np_y / density;
            vz = velocity_l[i].z - 0.02f * np_z / density;
            velocity_l[i] = new Vector3(vx, vy, vz);

            //位置の更新
            float px = 0;
            float py = 0;
            float pz = 0;
            //Δt=0.02で計算
            px = position_l[i].x - 0.02f * 0.02f * np_x / density;
            py = position_l[i].y - 0.02f * 0.02f * np_y / density;
            pz = position_l[i].z - 0.02f * 0.02f * np_z / density;
        }

        //計算結果を再現
        int index = 0;
        GameObject[] waters = GameObject.FindGameObjectsWithTag("Water");
        foreach (GameObject water in waters)
        {
            Transform mytransform = water.transform;
            Vector3 pos = mytransform.position;
            pos = position_l[index];
            //Debug.Log(position_l[index]);
            mytransform.position = pos;
            index++;
        }

        Debug.Log(roop_cnt);
    }
}
