# Henderson's mixed-model equations

Let $X$, $Z$ be real $n \times p$ and $n \times q$ matrices, let $G$ and $R$ be positive definite, and let $V = Z G Z^\top + R$ be the [phenotypic covariance](phen-cov.md). Then for all $y \in \mathbb{R}^n$, $b \in \mathbb{R}^p$ and $u \in \mathbb{R}^q$, the pair $(b, u)$ [solves the mixed-model equations](is-mmesolution.md) if and only if

- $X^\top V^{-1} X b = X^\top V^{-1} y$ (the generalized least-squares normal equations), and
- $u = G Z^\top V^{-1} (y - X b)$

(Henderson 1975; Robinson 1991).

## Sources

- C. R. Henderson, *Best linear unbiased estimation and prediction under a selection model*, Biometrics 31 (1975), 423–447.
- G. K. Robinson, *That BLUP is a good thing: the estimation of random effects*, Stat. Sci. 6 (1991), 15–32.
