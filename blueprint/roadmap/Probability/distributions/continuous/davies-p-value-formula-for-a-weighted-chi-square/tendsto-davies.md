# Gil-Pelaez inversion for a weighted chi-square law

Let $k$ be a finite index set, $\lambda \in \mathbb{R}^k$, and let $Q = \sum_j \lambda_j \xi_j^2$ with $\xi_j$ independent standard normal, so that $Q$ has the weighted chi-square law $\sum_j \lambda_j \chi^2_1$. Let $\varphi(t) = \prod_j (1 - 2 i \lambda_j t)^{-1/2}$ (principal branch) be its characteristic function. For every $q \in \mathbb{R}$, as $T \to \infty$,

$$\frac12 + \frac{1}{\pi} \int_0^T \frac{\operatorname{Im}\bigl(e^{-i t q} \varphi(t)\bigr)}{t} \, dt \;\longrightarrow\; \frac12 \bigl(P(Q > q) + P(Q \ge q)\bigr).$$

The limit is the midpoint form of Gil-Pelaez's inversion theorem: it is the upper tail $P(Q > q)$ only when $Q$ has no atom at $q$. For instance, with all weights $0$ and $q = 0$ the limit is $\frac12$, while $P(Q > 0) = 0$; the [nondegenerate case](tendsto-davies-of-ne-zero.md) has no atoms. This integral is the one Davies' algorithm discretizes.

## Sources

- J. Gil-Pelaez, Note on the inversion theorem, *Biometrika* 38 (1951), 481–482 (the inversion formula for the distribution function at a point, in the midpoint form).
- R. B. Davies, *Algorithm AS 155: The distribution of a linear combination of χ² random variables*, J. R. Stat. Soc. C 29 (1980), 323–333: eq. (1) defines the linear combination $Q$, and the algorithm evaluates its distribution function by numerical integration of this inversion integral.
