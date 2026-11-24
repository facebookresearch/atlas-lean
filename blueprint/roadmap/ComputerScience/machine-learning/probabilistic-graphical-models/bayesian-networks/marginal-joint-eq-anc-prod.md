# The law of an ancestral set depends only on its tables

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a finite nonempty
type $\alpha$ and joint distribution $P$. Let $A$ be an [ancestral](is-ancestral.md) finite set
of nodes, $Q_A$ the [product of the tables of $A$](anc-prod.md), and $S \subseteq A$. Then the
marginals of $P$ and $Q_A$ on $S$ agree: for every $x' \in \alpha^n$,
$\sum_{x \,:\, x_S = x'_S} P(x) = \sum_{x \,:\, x_S = x'_S} Q_A(x)$.
