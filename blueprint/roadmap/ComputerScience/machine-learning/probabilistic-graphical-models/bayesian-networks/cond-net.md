# The network of conditional tables of a law

Let $\alpha$ be a finite nonempty type, $P : \alpha^n \to \mathbb{R}$ with $P(x) \ge 0$ for all
$x$, and assign to each node $k$ a set $\mathrm{pa}(k) \subseteq \{0, \dots, k - 1\}$ of parents.
The network of conditional tables of $P$ is the Bayesian network with these parent sets whose
table at each node $k$ is [the conditional law of node $k$ given its parents](cond-table.md)
under $P$.
