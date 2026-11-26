# Factor-analytic and recursive parametrizations of a trait covariance matrix

Let $t\ge1$ be the number of traits.

**Factor analytic.** For a $t\times q$ loading matrix $W$ and $\Psi=\operatorname{diag}(\psi_{11},\ldots,\psi_{tt})$ with $\psi_{kk}\ge0$,

$$\Omega=WW^\top+\Psi$$

is symmetric positive semidefinite, and positive definite whenever every $\psi_{kk}>0$. A logical $t\times q$ pattern may force chosen loadings to zero (trait $k$ does not load on factor $l$).

**Recursive.** For a $t\times t$ matrix $W$ of recursive (regression) coefficients with $I-W$ invertible and $\Psi=\operatorname{diag}(\psi_{kk})$,

$$\Omega=(I-W)^{-1}\,\Psi\,\bigl((I-W)^{-1}\bigr)^\top,$$

the covariance of $e$ solving $e=We+\varepsilon$ with $\varepsilon\sim\mathrm{MVN}(0,\Psi)$.

**Fully recursive models are unstructured.** Let $W$ range over strictly lower-triangular matrices and $\Psi$ over diagonal matrices with positive diagonal. Then $(W,\Psi)\mapsto(I-W)^{-1}\Psi(I-W)^{-\top}$ is a bijection onto the set of $t\times t$ symmetric positive definite matrices.

## Depends on

- [Multitrait Bayesian regression with Gaussian, spike–slab and kernel priors](multitrait-bayesian-regression-with-gaussian-and-spike-slab-priors.md)

## Proof depends on

None beyond the quadratic-form computation and the unique $LDL^\top$ factorization of a symmetric positive definite matrix (Mathlib's `LDL` decomposition), as the Expansion describes.

## Expansion

- Factor analytic: $x^\top\Omega x=\|W^\top x\|^2+\sum_k\psi_{kk}x_k^2\ge0$, with equality forcing $x=0$ when every $\psi_{kk}>0$.
- Recursive: if $e=We+\varepsilon$ then $e=(I-W)^{-1}\varepsilon$ and $\operatorname{Cov}(e)=(I-W)^{-1}\Psi(I-W)^{-\top}$.
- Fully recursive: for strictly lower-triangular $W$, $L=(I-W)^{-1}$ is unit lower triangular, and every unit lower-triangular $L$ arises from exactly one such $W$, namely $W=I-L^{-1}$. Every symmetric positive definite $\Omega$ has a unique factorization $\Omega=L\Psi L^\top$ with $L$ unit lower triangular and $\Psi$ diagonal with positive entries (the $LDL^\top$ form of the Cholesky decomposition), which gives the bijection. Priors can then be placed on the recursive effects and the residual variances instead of an inverse-Wishart prior on $\Omega$; the paper notes that the inverse-Wishart prior can be influential when the sample is small and the number of traits large.

## Sources

- P. Pérez-Rodríguez, G. de los Campos, *Multitrait Bayesian shrinkage and variable selection models with the BGLR-R package*, Genetics 222 (2022), iyac112, <https://doi.org/10.1093/genetics/iyac112>, PMCID PMC9434216 (Table 2, Covariance structures; Discussion).
