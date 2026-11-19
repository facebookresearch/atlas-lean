# Step 1: homogeneity

Let $x_1, \dots, x_n \in \mathbb{R}^d$ have every coordinate in $[-1, 1]$, let $Q \ge 0$ and
$\sigma \in \{-1, 1\}^n$. Let $A_Q$ be the [path-norm ball](path-norm-ball-values.md) on the sample
and $N$ the set of value vectors of the [ReLU neurons on the $\ell^1$ unit ball](l1-neuron-values.md).
Then the correlation of every network of path norm at most $Q$ with $\sigma$ is at most $Q$ times
the sum of the suprema over $N$ for $\sigma$ and for $-\sigma$:

$$\sup_{v \in A_Q} \sum_i \sigma_i v_i \le Q \Big( \sup_{v \in N} \sum_i \sigma_i v_i + \sup_{v \in N} \sum_i (-\sigma_i) v_i \Big),$$

where a supremum of a set of reals that is unbounded above or empty is $0$.
