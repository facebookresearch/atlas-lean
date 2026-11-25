# Jacobi eigenbasis of the Wright–Fisher generator with mutation

Let $\theta_1, \theta_2 > 0$, $\theta = \theta_1 + \theta_2$, and let $L = \frac12x(1 - x)\partial_x^2 + \frac12(\theta_1 - \theta x)\partial_x$ be the [neutral generator with two-way mutation](spectral-structure-of-l-0-theta-on-polynomials.md). Let $R_n = R_n^{(\theta_1, \theta_2)}$, $n \ge 0$, be the [orthonormal shifted Jacobi polynomials](../transition-densities-of-wright-fisher-diffusions/jacobi-and-gegenbauer-polynomials-on-0-1.md) for the stationary law $\mathrm{Beta}(\theta_1, \theta_2)$. Then:

1. Each $R_n$ is an eigenfunction, $LR_n = -\lambda_nR_n$ with $\lambda_n = \frac12n(n - 1 + \theta)$, and the eigenvalues $0 = \lambda_0 < \lambda_1 < \lambda_2 < \cdots$ are distinct.
2. The family is orthonormal, $\mathbb E[R_m(Y)R_n(Y)] = \delta_{mn}$ for $Y \sim \mathrm{Beta}(\theta_1, \theta_2)$.
3. The family is complete: $(R_n)_{n \ge 0}$ is an orthonormal basis of $L^2(\mathrm{Beta}(\theta_1, \theta_2))$, so every $f$ in that space satisfies $f = \sum_n\langle f, R_n\rangle R_n$ in $L^2$ and $\|f\|^2 = \sum_n\langle f, R_n\rangle^2$.

Griffiths and Spanò (2010, Section 1) state the eigenvalue equation in the form $LP_n = -\frac12n(n + \theta - 1)P_n$ for these orthonormal polynomials; in their Dirichlet construction (Section 2), the two-type case is a complete orthonormal polynomial set on the Beta distribution.

## Depends on

- [Polynomial spectrum of the neutral Wright–Fisher generator with mutation](spectral-structure-of-l-0-theta-on-polynomials.md)
- [Orthonormal normalization of shifted Jacobi polynomials](../transition-densities-of-wright-fisher-diffusions/jacobi-and-gegenbauer-polynomials-on-0-1.md)

## Expansion

1. The eigenvalue equation is the Jacobi equation $x(1 - x)R_n'' + (\theta_1 - \theta x)R_n' = -n(n + \theta - 1)R_n$ divided by $2$; distinctness is $\lambda_n - \lambda_{n-1} = n - 1 + \theta/2 > 0$.
2. Completeness: $R_0, \dots, R_N$ span the polynomials of degree at most $N$, polynomials are uniformly dense in $C[0, 1]$ by Weierstrass approximation, and continuous functions are dense in $L^2$ of a finite measure on $[0, 1]$; uniform convergence implies $L^2$ convergence for a probability measure.
3. Orthonormality and completeness give the Parseval identity and the $L^2$ expansion.

## Sources

- R. C. Griffiths and D. Spanò, Diffusion processes and coalescent trees, in *Probability and Mathematical Genetics: Papers in Honour of Sir John Kingman*, Cambridge University Press (2010), Section 1, equations (1.1), (1.2) and (1.7), and Section 2, around (2.15)–(2.16). <https://arxiv.org/abs/1003.4650>
