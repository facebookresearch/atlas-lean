# Intervention preserves the law of the parents

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a finite nonempty type
$\alpha$ and joint distribution $P$, let $k$ be a node and $a \in \alpha$. For all values $z$ of
the parents of $k$,
$P_{\mathrm{do}(X_k = a)}(X_{\mathrm{pa}(k)} = z) = P(X_{\mathrm{pa}(k)} = z)$, where
$P_{\mathrm{do}(X_k = a)}$ is the joint distribution of the [intervention](intervene.md).
