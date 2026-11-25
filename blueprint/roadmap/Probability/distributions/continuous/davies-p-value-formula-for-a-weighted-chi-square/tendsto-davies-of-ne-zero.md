# Davies' formula, nondegenerate case

(Davies 1980, eq. (1).) Let $k$ be a finite index set, $\lambda \in \mathbb{R}^k$, and let $Q = \sum_j \lambda_j \xi_j^2$ with $\xi_j$ independent standard normal, so that $Q$ has the weighted chi-square law $\sum_j \lambda_j \chi^2_1$. Let $\varphi(t) = \prod_j (1 - 2 i \lambda_j t)^{-1/2}$ (principal branch) be its characteristic function. If $\lambda_j \ne 0$ for some $j$, then for every $q \in \mathbb{R}$, as $T \to \infty$,

$$\frac12 + \frac{1}{\pi} \int_0^T \frac{\operatorname{Im}\bigl(e^{-i t q} \varphi(t)\bigr)}{t} \, dt \;\longrightarrow\; P(Q > q).$$

If all weights are zero then $Q \equiv 0$, and at $q = 0$ the limit is the mid-p value $\tfrac12$, not $P(Q > 0) = 0$, so the nonzero-weight hypothesis is needed.

## Sources

R. B. Davies, *Algorithm AS 155: The distribution of a linear combination of χ² random variables*, J. R. Stat. Soc. C 29 (1980), 323–333, eq. (1).
