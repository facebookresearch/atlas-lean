# Weak-selection perturbation of the Wright–Fisher spectrum

Consider the Wright–Fisher diffusion with recurrent mutation and general diploid selection in the parametrization of Song and Steinrücken (2012, equations (26)–(31)): $L = L_0 + 2\sigma x(1 - x)[x + h(1 - 2x)]\partial_x$ with $L_0 = \frac12x(1 - x)\partial_x^2 + \frac12[\alpha(1 - x) - \beta x]\partial_x$, $\alpha, \beta > 0$, neutral speed density $\pi_0(x) = x^{\alpha - 1}(1 - x)^{\beta - 1}$, Jacobi eigenfunctions $R_n$ of $L_0$ with eigenvalues $-\lambda_n$, $\lambda_n = \frac12n(n + \alpha + \beta - 1)$, and selected speed density $\pi = e^{\bar\sigma}\pi_0$ with $\bar\sigma(x) = 2\sigma x[x + 2h(1 - x)]$. They show (equation (33)) that conjugation by $e^{-\bar\sigma/2}$ turns $L$ into the neutral operator plus a multiplication: $L(e^{-\bar\sigma/2}f) = -e^{-\bar\sigma/2}[(-L_0) + Q]f$ with the degree-four polynomial

$$Q(x) = \sigma\{h\alpha + [1 + \alpha - (2 + 3\alpha + \beta)h]x - (1 + \alpha + \beta)(1 - 2h)x^2\} + 2\sigma^2x(1 - x)(h + x - 2hx)^2.$$

Since $f \mapsto e^{\bar\sigma/2}f$ is unitary from $L^2(\pi)$ onto $L^2(\pi_0)$, the eigenvalues $\Lambda_0(\sigma) \le \Lambda_1(\sigma) \le \cdots$ of $-L$ are those of the self-adjoint operator $-L_0 + Q$ in $L^2(\pi_0)$, a bounded symmetric perturbation of $-L_0$. Two consequences follow. First, by the min–max principle, for every $\sigma$ and $h$ and every $n$,

$$|\Lambda_n(\sigma) - \lambda_n| \le \sup_{0 \le x \le 1}|Q(x)|,$$

a bound of order $|\sigma|$ as $\sigma \to 0$. Second, the $\lambda_n$ are simple, since $\lambda_{n+1} - \lambda_n = n + (\alpha + \beta)/2 > 0$, so each $\Lambda_n(\sigma)$ is analytic near $\sigma = 0$ and, by the first-order eigenvalue perturbation formula for symmetric operators (Kato 1976, Chapter VII), $\Lambda_n(\sigma) = \lambda_n + \sigma\langle R_n, Q_1R_n\rangle_{\pi_0}/\langle R_n, R_n\rangle_{\pi_0} + O(\sigma^2)$, where $Q_1$ is the coefficient of $\sigma$ in $Q$. Song and Steinrücken (2012, section on genic selection) note that Kimura (1955) used an equation of this kind to obtain perturbation expansions in powers of $\sigma$, whereas their method is not perturbative.

## Depends on

- [Transition density of the Wright–Fisher diffusion with diploid selection](../../../../Biology/population-genetics/diffusion-theory/transition-densities-of-wright-fisher-diffusions/transition-density-with-diploid-selection.md)
- [Jacobi eigenbasis of the Wright–Fisher generator with mutation](../wright-fisher-diffusion-with-mutation/jacobi-eigenbasis-with-mutation.md)

## Expansion

1. The unitary map $f \mapsto e^{\bar\sigma/2}f$ from $L^2(\pi)$ to $L^2(\pi_0)$ and the conjugated operator $-L_0 + Q$.
2. The min–max bound on the shift of every ordered eigenvalue by $\sup|Q|$.
3. Simplicity of the neutral eigenvalues, analyticity of $\Lambda_n(\sigma)$ near $0$, and the first-order coefficient $\langle R_n, Q_1R_n\rangle_{\pi_0}/\langle R_n, R_n\rangle_{\pi_0}$.
4. The second-order coefficient and the corresponding eigenfunction corrections, with the radius of analyticity bounded below by the gaps $\lambda_{n+1} - \lambda_n$.

## Sources

- Y. S. Song and M. Steinrücken, A simple method for finding explicit analytic transition densities of diffusion processes with general diploid selection, Genetics 190 (2012), 1117–1129, equations (26)–(33) and the section on genic selection. <https://doi.org/10.1534/genetics.111.136929>
- T. Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Grundlehren der mathematischen Wissenschaften 132, Springer, 1976, Chapter VII (analytic perturbation theory, selfadjoint holomorphic families).
