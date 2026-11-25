# Back-door adjustment for a set of predecessors containing the parents

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a finite nonempty type
$\alpha$ and joint distribution $P$, let $k$ be a node, $a \in \alpha$, and let $Z$ be a finite
set of nodes preceding $k$ in the topological order (so $Z$ contains no descendant of $k$) that
contains the parents of $k$. Then $Z$ meets the back-door criterion for every outcome node
$y \notin Z$ (a path from $k$ to $y$ that starts with an arrow into $k$ starts $k \leftarrow p$
with $p \in \mathrm{pa}(k) \subseteq Z$, an interior non-collider, so it is blocked). Assume that
$P(X_k = a, X_Z = z) \ne 0$ whenever $P(X_Z = z) \ne 0$. Then for every
$f : \alpha^n \to \mathbb{R}$,

$$\sum_x P_{\mathrm{do}(X_k = a)}(x) f(x) = \sum_{z \in \alpha^Z} P(X_Z = z) \, \frac{\sum_{x \,:\, x_k = a,\, x_Z = z} P(x) f(x)}{P(X_k = a, X_Z = z)},$$

that is, $E[f \mid \mathrm{do}(X_k = a)] = \sum_z P(X_Z = z) \, E[f \mid X_k = a, X_Z = z]$ (Pearl
2009, Theorem 3.3.2, in this case), where a term with $P(X_Z = z) = 0$ is $0$.
