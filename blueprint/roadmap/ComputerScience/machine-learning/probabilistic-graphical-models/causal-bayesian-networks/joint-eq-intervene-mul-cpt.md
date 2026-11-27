# Joint law as interventional law times the node's table

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a nonempty type
$\alpha$ and joint distribution $P$, let $P_{\mathrm{do}(X_k = a)}$ be the joint distribution of
the [intervention](intervene.md) $\mathrm{do}(X_k = a)$, and write $p_k(\cdot \mid z)$ for the
table of node $k$ at values $z$ of its parents. For every $x \in \alpha^n$ with $x_k = a$,

$$P(x) = P_{\mathrm{do}(X_k = a)}(x) \, p_k(a \mid x_{\mathrm{pa}(k)}).$$
