# Low-degree likelihood ratio and low-degree advantage

A **testing problem** is a sequence of pairs of distributions $(\mathbb{Q}_n, \mathbb{P}_n)$ on $\mathbb{R}^{N_n}$ (null and planted), with $\mathbb{P}_n \ll \mathbb{Q}_n$ and likelihood ratio $L_n = d\mathbb{P}_n/d\mathbb{Q}_n \in L^2(\mathbb{Q}_n)$. **Strong detection** means a test with $\mathbb{Q}_n(\text{reject}) + \mathbb{P}_n(\text{accept}) \to 0$; **weak detection** means this sum is at most $1 - \Omega(1)$. Let $V_n^{\le D}$ be the set of polynomials of degree at most $D$ in the coordinates of $Y \in \mathbb{R}^{N_n}$ that are square-integrable under $\mathbb{Q}_n$, identified when they agree $\mathbb{Q}_n$-almost everywhere; it is a finite-dimensional subspace of $L^2(\mathbb{Q}_n)$, with inner product $\langle f, g\rangle = \mathbb{E}_{\mathbb{Q}_n}[fg]$ (KWB Definition 1.14), and it need not contain every polynomial: if $\mathbb{Q}_n$ has Cauchy coordinates, $f(Y) = Y_1$ is not in it. The **low-degree likelihood ratio** $L_n^{\le D}$ is the orthogonal projection of $L_n$ onto $V_n^{\le D}$, and the **degree-$D$ advantage** is $\|L_n^{\le D}\| = \sqrt{\mathbb{E}_{\mathbb{Q}_n}[(L_n^{\le D})^2]}$. Equivalently,

$$
\|L_n^{\le D}\| = \max_{f \in V_n^{\le D},\ \mathbb{E}_{\mathbb{Q}_n}[f^2] > 0} \frac{\mathbb{E}_{\mathbb{P}_n}[f]}{\sqrt{\mathbb{E}_{\mathbb{Q}_n}[f^2]}},
$$

so $\|L_n^{\le D}\|$ measures how well any degree-$D$ polynomial statistic separates the planted from the null distribution in mean relative to its null standard deviation.

## Sources

- D. Kunisky, A. S. Wein, A. S. Bandeira, "Notes on Computational Hardness of Hypothesis Testing: Predictions Using the Low-Degree Likelihood Ratio", Mathematical Analysis, its Applications and Computation, Springer (2022), arXiv:1907.11636.
- S. B. Hopkins, "Statistical Inference and the Sum of Squares Method", PhD thesis, Cornell University (2018).
