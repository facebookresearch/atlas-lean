# $q = 1$ measure equals Bernoulli percolation on graph-edge events

Let $G$ be a simple graph on a finite vertex set $V$, let $\mathcal{P}$ be the set of unordered pairs of elements of $V$ and let $0 < p < 1$. Let $\phi_{G, p, 1}$ be the [$q = 1$ random-cluster weight](fk-prob-one-pattern.md) on $\{0, 1\}^{\mathcal{P}}$, proportional to $\prod_{e \in E(G)} p^{\omega(e)} (1 - p)^{1 - \omega(e)}$: its marginal on the edges of $G$ is the random-cluster measure with $q = 1$ and its coordinates off the edges of $G$ are independent and uniform. If $A \subseteq \{0, 1\}^{\mathcal{P}}$ depends only on the coordinates indexed by edges of $G$, then

$$\phi_{G, p, 1}(A) = \mathbb{P}_p(A),$$

where $\mathbb{P}_p$ is the [Bernoulli product measure](../../../random-fields/bernoulli-product-measures-and-cylinder-events/bernoulli-product-measure.md) with parameter $p$ on $\{0, 1\}^{\mathcal{P}}$.
