# Adjustment for the direct causes

**Adjustment for the direct causes** (Pearl 2009, Theorem 3.2.2; the case $Z = \mathrm{pa}(X)$ of
the back-door adjustment): let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with
values in a finite nonempty type $\alpha$ and joint distribution $P$, let $k$ be a node and
$a \in \alpha$, and assume $P(X_k = a, X_{\mathrm{pa}(k)} = z) \ne 0$ whenever
$P(X_{\mathrm{pa}(k)} = z) \ne 0$. Then for every $f : \alpha^n \to \mathbb{R}$,

$$\sum_x P_{\mathrm{do}(X_k = a)}(x) f(x) = \sum_{z} P(X_{\mathrm{pa}(k)} = z) \, \frac{\sum_{x \,:\, x_k = a,\, x_{\mathrm{pa}(k)} = z} P(x) f(x)}{P(X_k = a, X_{\mathrm{pa}(k)} = z)},$$

that is, $E[f \mid \mathrm{do}(X_k = a)] = \sum_z P(X_{\mathrm{pa}(k)} = z) \, E[f \mid X_k = a, X_{\mathrm{pa}(k)} = z]$,
where $z$ runs over the values of the parents of $k$ and a term with
$P(X_{\mathrm{pa}(k)} = z) = 0$ is $0$.
