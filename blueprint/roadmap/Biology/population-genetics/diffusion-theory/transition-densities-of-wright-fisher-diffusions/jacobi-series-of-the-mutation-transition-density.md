# Jacobi series of the Wright–Fisher transition density with mutation

Let $\theta_1, \theta_2 > 0$, $\theta = \theta_1 + \theta_2$, let $\pi = \mathrm{Beta}(\theta_1, \theta_2)$ with density $\pi(y)$, and let $R_n$ and $\lambda_n = \frac12n(n - 1 + \theta)$ be the [Jacobi eigenbasis](../wright-fisher-diffusion-with-mutation/jacobi-eigenbasis-with-mutation.md) of the generator $L = \frac12x(1 - x)\partial_x^2 + \frac12(\theta_1 - \theta x)\partial_x$. For $t > 0$, $x \in [0, 1]$ and $y \in (0, 1)$ define

$$f_t(x, y) = \pi(y)\Bigl(1 + \sum_{n \ge 1}e^{-\lambda_nt}R_n(x)R_n(y)\Bigr).$$

1. For every $t_0 > 0$ the series $\sum_ne^{-\lambda_nt}R_n(x)R_n(y)$ converges absolutely and uniformly on $[t_0, \infty) \times [0, 1]^2$.
2. For every solution $X$ of the [martingale problem with mutation](../wright-fisher-diffusion-with-mutation/two-way-mutation-and-selection-wright-fisher-mar.md) (zero selection) with $X_0 = x$, and every $t > 0$, the law of $X_t$ is $f_t(x, y)\,dy$; equivalently $f_t(x, \cdot)$ is the density of the [Beta-mixture kernel](line-of-descent-mixture-representation-of-the-tr.md) $K_t(x, \cdot)$.
3. Consequently $f_t(x, y) \ge 0$ and $\int_0^1f_t(x, y)\,dy = 1$; $f_t(x, y)\,dy \to \delta_x$ weakly as $t \downarrow 0$; and the Chapman–Kolmogorov equation $\int_0^1f_s(x, z)f_t(z, y)\,dz = f_{s+t}(x, y)$ holds for $s, t > 0$.
4. As $t \to \infty$, the ratio $f_t(x, y)/\pi(y)$ converges to $1$ uniformly in $x \in [0, 1]$, $y \in (0, 1)$, with $\sup_{x, y}|f_t(x, y)/\pi(y) - 1| = O(e^{-\lambda_1t})$ and $\lambda_1 = \theta/2$; hence $f_t(x, \cdot) \to \pi$ uniformly on compact subsets of $(0, 1)$ and in total variation. Uniform convergence of $f_t$ itself on $(0, 1)$ fails when $\pi$ is unbounded, for instance when $\theta_1 < 1$.

This is the eigenfunction expansion (1.3) of Griffiths and Spanò (2010), shown here to be the transition density of the diffusion rather than a formal solution of its Kolmogorov equations; their (2.1) is the second, mixture form of the same density.

## Depends on

- [Jacobi eigenbasis of the Wright–Fisher generator with mutation](../wright-fisher-diffusion-with-mutation/jacobi-eigenbasis-with-mutation.md)
- [Beta-mixture marginals for every mutation Wright-Fisher solution](line-of-descent-mixture-representation-of-the-tr.md)
- [Martingale problem with selection and mutation](../wright-fisher-diffusion-with-mutation/two-way-mutation-and-selection-wright-fisher-mar.md)

## Expansion

1. Uniform convergence: the orthonormal Jacobi polynomials are bounded on $[0, 1]$ by a polynomial in $n$. With $a = \theta_2 - 1$, $b = \theta_1 - 1$ and $q = \max(a, b)$, the classical bound is $\max_{[-1,1]}|P_n^{(a,b)}| = \binom{n + q}{n}$ when $q \ge -\frac12$, and $O(n^{-1/2})$ when $q < -\frac12$ (Szegő, Theorem 7.32.1); the normalizing constant grows polynomially. The factor $e^{-\lambda_nt_0}$ decays like $e^{-n^2t_0/2}$.
2. Coefficients of the true law: since $R_n$ is a polynomial eigenfunction, the martingale problem gives $\frac{d}{dt}\mathbb E_x[R_n(X_t)] = \mathbb E_x[LR_n(X_t)] = -\lambda_n\mathbb E_x[R_n(X_t)]$, so $\mathbb E_x[R_n(X_t)] = e^{-\lambda_nt}R_n(x)$. The density of $K_t(x, \cdot)$ with respect to $\pi$ is bounded for $t > 0$, hence in $L^2(\pi)$: the density of each component $\mathrm{Beta}(\theta_1 + l, \theta_2 + n - l)$ with respect to $\pi$ is at most a polynomial in $n$ times $2^n$, against mixture weights $q_n^\theta(t)$ of order $e^{-n^2t/2}$. It has these coefficients; completeness identifies it with $f_t(x, \cdot)/\pi$ in $L^2(\pi)$, and continuity of both sides gives equality everywhere.
3. Positivity and normalization follow from the mixture; the small-time limit from the concentration of the Beta mixture at $x$ as the entrance-from-infinity line count grows; Chapman–Kolmogorov from orthonormality, integrating the two uniformly convergent series term by term.
4. The large-time bound is the first term of the series, the polynomial growth bound controlling the remainder.

## Sources

- R. C. Griffiths and D. Spanò, Diffusion processes and coalescent trees, in *Probability and Mathematical Genetics: Papers in Honour of Sir John Kingman*, Cambridge University Press (2010), Section 1, equations (1.3)–(1.4), and Section 2, equation (2.1). <https://arxiv.org/abs/1003.4650>
