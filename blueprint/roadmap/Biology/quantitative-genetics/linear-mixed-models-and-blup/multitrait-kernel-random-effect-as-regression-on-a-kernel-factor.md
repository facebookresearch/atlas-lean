# Multitrait kernel random effect as a Gaussian regression on a factor of the kernel

Let $K$ be a symmetric positive semidefinite $n\times n$ matrix and let $X$ be any real $n\times r$ matrix with $XX^\top=K$; for example $X=\Gamma\Lambda^{1/2}$ from an eigendecomposition $K=\Gamma\Lambda\Gamma^\top$ (scaled eigenvectors), or a Cholesky factor. Let $\Omega$ be a $t\times t$ covariance matrix and let $B$ be an $r\times t$ random matrix whose rows are independent $\mathrm{MVN}(0,\Omega)$. Then $U=XB$ satisfies

$$\operatorname{vec}(U)\sim\mathrm{MVN}(0,\ \Omega\otimes K),$$

where $\operatorname{vec}$ stacks columns. Hence a multitrait random effect with prior $\operatorname{vec}(U)\sim\mathrm{MVN}(0,\Omega\otimes K)$ (a multitrait GBLUP or other kernel model) can be fitted as a Gaussian regression of the traits on the columns of $X$ with prior rows $b_j\sim\mathrm{MVN}(0,\Omega)$; with $X=\Gamma\Lambda^{1/2}$, columns with $\lambda_j=0$ may be dropped.

## Depends on

- [Multitrait Bayesian regression with Gaussian, spike–slab and kernel priors](multitrait-bayesian-regression-with-gaussian-and-spike-slab-priors.md)

## Proof depends on

None beyond the covariance of $\operatorname{vec}(XB)$ and the mixed-product rule for Kronecker products, as the Expansion describes.

## Expansion

- Since the rows of $B$ are independent with covariance $\Omega$, $\operatorname{Cov}(B_{jk},B_{j'k'})=[j=j']\,\Omega_{kk'}$, that is $\operatorname{Cov}(\operatorname{vec}B)=\Omega\otimes I_r$.
- $\operatorname{vec}(XB)=(I_t\otimes X)\operatorname{vec}(B)$ is Gaussian with mean $0$ and covariance $(I_t\otimes X)(\Omega\otimes I_r)(I_t\otimes X^\top)=\Omega\otimes XX^\top=\Omega\otimes K$ by the mixed-product rule.
- Computationally, the regression form costs the same per Gibbs sweep as a Gaussian regression with $n$ observations and $r\le n$ predictors, plus a one-time factorization of $K$; the paper recommends the kernel form only when $n$ is not too large and much smaller than the number of SNPs.

## Sources

- P. Pérez-Rodríguez, G. de los Campos, *Multitrait Bayesian shrinkage and variable selection models with the BGLR-R package*, Genetics 222 (2022), iyac112, <https://doi.org/10.1093/genetics/iyac112>, PMCID PMC9434216 (Equations 4–5; section on computational performance of kernel models).
