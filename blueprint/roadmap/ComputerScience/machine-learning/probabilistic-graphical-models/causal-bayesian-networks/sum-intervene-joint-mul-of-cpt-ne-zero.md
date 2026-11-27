# Adjustment for the direct causes under table positivity

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a finite nonempty type
$\alpha$ and joint distribution $P$, let $k$ be a node and $a \in \alpha$ such that the table of
$k$ gives $a$ nonzero probability at every value of the parents of $k$, and let
$f : \alpha^n \to \mathbb{R}$. Then

$$\sum_x P_{\mathrm{do}(X_k = a)}(x) f(x) = \sum_{z} P(X_{\mathrm{pa}(k)} = z) \, \frac{\sum_{x \,:\, x_k = a,\, x_{\mathrm{pa}(k)} = z} P(x) f(x)}{P(X_k = a, X_{\mathrm{pa}(k)} = z)},$$

where $z$ runs over the values of the parents of $k$, $P_{\mathrm{do}(X_k = a)}$ is the joint
distribution of the [intervention](intervene.md) and $P(E)$ is the sum of $P(x)$ over $x \in E$.
