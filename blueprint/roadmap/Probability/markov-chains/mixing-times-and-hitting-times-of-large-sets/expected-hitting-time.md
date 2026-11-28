# Hitting-time sum of a set

Let $n \in \mathbb{N}$, let $P$ be a real $n \times n$ matrix, $A \subseteq \{1, \dots, n\}$ and $x$ a state. The hitting-time sum of $A$ from $x$ is

$$h_A(x) = \sum_{t = 0}^{\infty} \max\big(P_x(\tau_A > t), 0\big) \in [0, \infty],$$

where $P_x(\tau_A > t)$ is $0$ for $x \in A$ and otherwise the row sum $\sum_z (P_A^{\,t})(x, z)$ of the $t$-th power of $P$ killed on $A$. The sum is taken in the extended nonnegative reals, after the positive part of each term. When $P$ is a transition matrix the terms are survival probabilities, already nonnegative, and $h_A(x)$ is the expected hitting time $\mathbb{E}_x[\tau_A]$ of $A$ from $x$.
