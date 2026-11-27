# Low-degree likelihood ratio and low-degree advantage

A **testing problem** is a sequence of pairs of distributions $(\mathbb{Q}_n, \mathbb{P}_n)$ on $\mathbb{R}^{N_n}$ (null and planted), with $\mathbb{P}_n \ll \mathbb{Q}_n$ and likelihood ratio $L_n = d\mathbb{P}_n/d\mathbb{Q}_n \in L^2(\mathbb{Q}_n)$. **Strong detection** means a test with $\mathbb{Q}_n(\text{reject}) + \mathbb{P}_n(\text{accept}) \to 0$; **weak detection** means this sum is at most $1 - \Omega(1)$. Let $\mathbb{R}[Y]_{\le D}$ be the polynomials of degree at most $D$ in the coordinates of $Y \in \mathbb{R}^{N_n}$, viewed as a subspace of $L^2(\mathbb{Q}_n)$ with inner product $\langle f, g\rangle = \mathbb{E}_{\mathbb{Q}_n}[fg]$. The **low-degree likelihood ratio** $L_n^{\le D}$ is the orthogonal projection of $L_n$ onto $\mathbb{R}[Y]_{\le D}$, and the **degree-$D$ advantage** is $\|L_n^{\le D}\| = \sqrt{\mathbb{E}_{\mathbb{Q}_n}[(L_n^{\le D})^2]}$. Equivalently,

$$
\|L_n^{\le D}\| = \max_{f \in \mathbb{R}[Y]_{\le D},\, f \ne 0} \frac{\mathbb{E}_{\mathbb{P}_n}[f]}{\sqrt{\mathbb{E}_{\mathbb{Q}_n}[f^2]}},
$$

so $\|L_n^{\le D}\|$ measures how well any degree-$D$ polynomial statistic separates the planted from the null distribution in mean relative to its null standard deviation.

## Sources

- D. Kunisky, A. S. Wein, A. S. Bandeira, "Notes on Computational Hardness of Hypothesis Testing: Predictions Using the Low-Degree Likelihood Ratio", Mathematical Analysis, its Applications and Computation, Springer (2022), arXiv:1907.11636.
- S. B. Hopkins, "Statistical Inference and the Sum of Squares Method", PhD thesis, Cornell University (2018).
