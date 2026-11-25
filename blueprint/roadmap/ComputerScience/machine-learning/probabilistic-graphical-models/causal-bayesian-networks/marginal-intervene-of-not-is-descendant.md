# Intervening on a node does not change the law of its non-descendants

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a finite nonempty type
$\alpha$ and joint distribution $P$, let $k$ be a node, $a \in \alpha$, and $S$ a finite set of
nodes none of which is a descendant of $k$. Then the marginal on $S$ of the joint distribution of
the [intervention](intervene.md) $\mathrm{do}(X_k = a)$ equals that of $P$: for every
$x' \in \alpha^n$, the total probability of the configurations agreeing with $x'$ on $S$ is the
same under both laws.
