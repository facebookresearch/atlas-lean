# Expected hitting time of a set

Let $n \in \mathbb{N}$, let $P$ be a real $n \times n$ matrix, $A \subseteq \{1, \dots, n\}$ and $x$ a state. The expected hitting time of $A$ from $x$ is

$$\mathbb{E}_x[\tau_A] = \sum_{t = 0}^{\infty} \max\big(P_x(\tau_A > t), 0\big) \in [0, \infty],$$

where $P_x(\tau_A > t)$ is $0$ for $x \in A$ and otherwise the row sum $\sum_z (P_A^{\,t})(x, z)$ of the $t$-th power of $P$ killed on $A$. The sum is taken in the extended nonnegative reals; for a transition matrix the terms are nonnegative.
