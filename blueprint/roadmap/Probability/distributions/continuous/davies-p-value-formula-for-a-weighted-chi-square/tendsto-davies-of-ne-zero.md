# Gil-Pelaez inversion for a weighted chi-square law, nondegenerate case

Let $k$ be a finite index set, $\lambda \in \mathbb{R}^k$, and let $Q = \sum_j \lambda_j \xi_j^2$ with $\xi_j$ independent standard normal, so that $Q$ has the weighted chi-square law $\sum_j \lambda_j \chi^2_1$. Let $\varphi(t) = \prod_j (1 - 2 i \lambda_j t)^{-1/2}$ (principal branch) be its characteristic function. If $\lambda_j \ne 0$ for some $j$, then for every $q \in \mathbb{R}$, as $T \to \infty$,

$$\frac12 + \frac{1}{\pi} \int_0^T \frac{\operatorname{Im}\bigl(e^{-i t q} \varphi(t)\bigr)}{t} \, dt \;\longrightarrow\; P(Q > q).$$

A nonzero weight makes the law of $Q$ atom-free, so the [midpoint form of the inversion](tendsto-davies.md) reduces to the upper tail. Davies' algorithm computes the distribution function $P(Q < q)$; in this atom-free case the upper-tail p-value is its complement.

## Sources

- J. Gil-Pelaez, Note on the inversion theorem, *Biometrika* 38 (1951), 481–482 (the inversion formula for the distribution function at a point, for a point without mass).
- R. B. Davies, *Algorithm AS 155: The distribution of a linear combination of χ² random variables*, J. R. Stat. Soc. C 29 (1980), 323–333: eq. (1) defines the linear combination $Q$, and the algorithm evaluates its distribution function by numerical integration of this inversion integral.
