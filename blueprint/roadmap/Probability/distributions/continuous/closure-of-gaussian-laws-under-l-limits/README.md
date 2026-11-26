# Closure of Gaussian laws under $L^2$ limits

Let $(\Omega, P)$ be a measure space and $E$ a separable real Banach space with its Borel $\sigma$-algebra. Let $X_n : \Omega \to E$ ($n \in \mathbb{N}$) be random vectors with Gaussian laws under $P$: the image of the law of $X_n$ under every continuous linear functional is a real Gaussian law, possibly degenerate (a point mass); this forces $P$ to be a probability measure. If $Y : \Omega \to E$ is almost everywhere strongly measurable and $\|X_n - Y\|_{L^2(P)} \to 0$, then $Y$ has a Gaussian law.

## Idea

Gaussian variables are often built as limits: Wiener integrals, series expansions of Brownian motion, closed linear spans of a Gaussian family. This result says that the limit stays Gaussian. In the real case, convergence in $L^2$ makes the means and the variances converge, and it gives convergence in distribution. The characteristic functions $e^{itm_n - \sigma_n^2 t^2/2}$ of the $X_n$ therefore converge both to the characteristic function of $Y$ and to the Gaussian one with the limiting mean and variance, so the two agree. A zero limiting variance is allowed and gives a point mass. In a Banach space, every continuous linear functional $L$ satisfies $\|L(X_n) - L(Y)\|_{L^2} \le \|L\| \, \|X_n - Y\|_{L^2}$, so the real case applies to each $L(Y)$.

## Statements

- [Closure of Gaussian laws under $L^2$ limits](of-tendsto-e-lp-norm.md)
- [Closure of real Gaussian laws under $L^2$ limits](of-tendsto-e-lp-norm-real.md): real case
- [Closure of Gaussian processes under $L^2$ limits](of-tendsto-e-lp-norm-2.md): process version
- [Continuity of the second moment pairing in $L^2$](tendsto-integral-mul-of-tendsto-e-lp-nor.md): lemma: continuity of second moments in $L^2$, the reason the variances converge in the argument above
