# Transition kernel of a stochastic matrix

Let $P$ be a [stochastic matrix](../kolmogorov-s-criterion-for-reversibility/stochastic-matrix.md)
on the states $S = \{0, 1, \dots, M\}$. Its transition kernel $\kappa_P$ from $S$ to $S$ is

$$\kappa_P(x, \cdot) = \sum_{j \in S} P(x, j) \, \delta_j ,$$

the measure on $S$ putting mass $P(x, j)$ on each state $j$. Since the entries are nonnegative
and the rows sum to $1$, each $\kappa_P(x, \cdot)$ is a probability measure: $\kappa_P$ is a
Markov kernel, the kernel form of the transition matrix.
