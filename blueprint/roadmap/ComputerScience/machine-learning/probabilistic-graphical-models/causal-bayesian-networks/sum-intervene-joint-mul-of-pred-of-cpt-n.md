# Back-door adjustment for a set of predecessors

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a finite nonempty type
$\alpha$ and joint distribution $P$, let $k$ be a node and $a \in \alpha$ such that the table of
$k$ gives $a$ nonzero probability at every value of the parents of $k$, let $Z$ be a finite set of
nodes $i < k$ containing the parents of $k$, and let $f : \alpha^n \to \mathbb{R}$. Then

$$\sum_x P_{\mathrm{do}(X_k = a)}(x) f(x) = \sum_{z \in \alpha^Z} P(X_Z = z) \, \frac{\sum_{x \,:\, x_k = a,\, x_Z = z} P(x) f(x)}{P(X_k = a, X_Z = z)},$$

where $P_{\mathrm{do}(X_k = a)}$ is the joint distribution of the [intervention](intervene.md) and
$P(E)$ is the sum of $P(x)$ over $x \in E$.
