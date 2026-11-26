# RHE-reg: randomized Haseman–Elston regression

Let $X$ be an $N\times M$ matrix of standardized genotypes, $y$ a centred phenotype and $y = X\beta + \epsilon$ with $\epsilon \sim N(0,\sigma_e^2 I_N)$ and $\beta \sim N(0, \frac{\sigma_g^2}{M} I_M)$, so that $\operatorname{cov}(y) = \sigma_g^2 K + \sigma_e^2 I_N$ with $K = XX^\top/M$.

**Haseman–Elston (cross-product) estimator.** Matching $yy^\top$ to its expectation in Frobenius norm,

$$(\hat\sigma_g^2, \hat\sigma_e^2) = \arg\min\left\|yy^\top - \sigma_g^2K - \sigma_e^2 I_N\right\|_F^2,$$

gives the normal equations

$$\begin{pmatrix}\operatorname{tr}(K^2) & \operatorname{tr}(K)\\ \operatorname{tr}(K) & N\end{pmatrix}\begin{pmatrix}\hat\sigma_g^2\\ \hat\sigma_e^2\end{pmatrix} = \begin{pmatrix} y^\top K y\\ y^\top y\end{pmatrix},$$

and, when $\operatorname{tr}(K) = N$ (standardized genotypes), $\hat\sigma_g^2 = \dfrac{y^\top(K - I)y}{\operatorname{tr}(K^2) - N}$.

**Randomized estimator.** $\operatorname{tr}(K)$ and $y^\top K y = \|X^\top y\|^2/M$ cost $O(NM)$. RHE-reg replaces $\operatorname{tr}(K^2)$ by the Hutchinson estimate

$$L_B = \frac{1}{BM^2}\sum_{b=1}^B\left\|XX^\top z_b\right\|_2^2, \qquad z_b \overset{\text{iid}}{\sim} N(0, I_N),$$

and solves the same normal equations with $L_B$ in place of $\operatorname{tr}(K^2)$, for total cost $O(NMB)$. The estimate is biased, with bias vanishing as $B$ grows, and its variance is approximately

$$\operatorname{Var}(\tilde\sigma_g^2) \approx \operatorname{Var}(\hat\sigma_g^2) + \frac{1}{B}\frac{\sigma_g^4\operatorname{tr}(K^2)}{(\operatorname{tr}(K^2) - N)^2}.$$

SNP heritability is reported as $\tilde\sigma_g^2/s_y^2$ with $s_y^2 = y^\top y/(N-1)$.

## Remarks

The Frobenius objective is a least-squares regression of the $N^2$ entries of $yy^\top$ on those of $K$ and $I$; its Gram matrix has entries $\langle K,K\rangle_F = \operatorname{tr}(K^2)$, $\langle K, I\rangle_F = \operatorname{tr}(K)$, $\langle I,I\rangle_F = N$, and right-hand sides $\langle yy^\top, K\rangle_F = y^\top K y$, $\langle yy^\top, I\rangle_F = y^\top y$. Eliminating $\hat\sigma_e^2$ with $\operatorname{tr}(K) = N$ gives the closed form. Forming $K$ is the $O(MN^2)$ bottleneck of exact Haseman–Elston regression; only $\operatorname{tr}(K^2)$ needs it, and the randomized trace removes that need. Because each genotype entry lies in $\{0,1,2\}$, the products $X^\top z_b$ can be accelerated further with the Mailman algorithm. The estimator uses only the second moment of the SNP effects, so it remains valid beyond the infinitesimal model.

## Depends on

- [Hutchinson's randomized trace estimator](hutchinson-randomized-trace-estimator.md)
- [Genetic relationship matrix](grm.md)
- [GREML covariance matrix $\sigma_g^2 K + \sigma_e^2 I$](greml-cov.md)

## Sources

- Y. Wu and S. Sankararaman, "A scalable estimator of SNP heritability for biobank-scale data", Bioinformatics (2018), Sections 2.1–2.4, Equations 1–11, <https://doi.org/10.1093/bioinformatics/bty253> (PMC6022682).
