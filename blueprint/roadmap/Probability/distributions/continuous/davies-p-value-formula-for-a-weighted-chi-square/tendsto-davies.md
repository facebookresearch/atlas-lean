# Davies' p-value formula

(Davies 1980, eq. (1), from Gil-Pelaez's inversion theorem.) Let $k$ be a finite index set, $\lambda \in \mathbb{R}^k$, and let $Q = \sum_j \lambda_j \xi_j^2$ with $\xi_j$ independent standard normal, so that $Q$ has the weighted chi-square law $\sum_j \lambda_j \chi^2_1$. Let $\varphi(t) = \prod_j (1 - 2 i \lambda_j t)^{-1/2}$ (principal branch) be its characteristic function. For every $q \in \mathbb{R}$, as $T \to \infty$,

$$\frac12 + \frac{1}{\pi} \int_0^T \frac{\operatorname{Im}\bigl(e^{-i t q} \varphi(t)\bigr)}{t} \, dt \;\longrightarrow\; \frac12 \bigl(P(Q > q) + P(Q \ge q)\bigr).$$

The improper integral is the one Davies' algorithm discretizes.
