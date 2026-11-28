# Lewis–Rossi–Weitsman theorem on paths with finite reciprocal integrals

This settles [Erdős Problem 515 on paths with finite reciprocal integrals](path-with-finite-reciprocal-integrals.md) in the affirmative: its statement holds.

For every entire function $f$ that is not a polynomial there is one path $\gamma : [0, \infty) \to \mathbb{C}$, parametrized by arc length (the variation of $\gamma$ on $[s, t]$ is $t - s$ whenever $0 \le s \le t$) and with $|\gamma(t)| \to \infty$ as $t \to \infty$, such that

$$
\int_0^\infty |f(\gamma(t))|^{-\lambda} \, dt < \infty \quad \text{for every } \lambda > 0.
$$

The same path serves every $\lambda$.

This is a case of Theorem 1 of Lewis, Rossi and Weitsman. For a function $u$ subharmonic in the plane whose radial maximum satisfies $\max_{|z| = r} u(z) / \log r \to \infty$ as $r \to \infty$, they give a single path to $\infty$ along which $\int e^{-\lambda u} \, |dz| < \infty$ for every $\lambda > 0$. Take $u = \log |f|$: it is subharmonic, $e^{-\lambda u} = |f|^{-\lambda}$, and since $f$ is not a polynomial, $\log M(r) / \log r \to \infty$, where $M(r)$ is the maximum of $|f|$ on $|z| = r$. The growth hypothesis cannot be dropped: for $u = 0$ the integral is the length of a path to $\infty$, which is infinite.

Earlier, Huber found for each single $\lambda > 0$ a path $C_\lambda$, depending on $\lambda$, with finite integral, and Zhang proved the statement above for $f$ of finite order.

## Sources

- T. F. Bloom, Erdős Problems, Problem #515, https://www.erdosproblems.com/515 (status PROVED); resolution: J. Lewis, J. Rossi and A. Weitsman, On the growth of subharmonic functions along paths, Ark. Mat. 22 (1984), 109-119, Theorem 1, https://doi.org/10.1007/BF02384375; erdosproblems.com/515: Huber proved that for every λ > 0 there is such a path C_λ, the finite-order case is due to Zhang (1977), and the general case to Lewis, Rossi and Weitsman, with |f| replaced by e^u for subharmonic u.
