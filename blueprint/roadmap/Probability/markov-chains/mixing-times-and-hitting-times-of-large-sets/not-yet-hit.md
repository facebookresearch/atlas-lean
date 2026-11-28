# Probability of not yet hitting a set

Let $n \in \mathbb{N}$, let $P$ be a real $n \times n$ matrix, $A \subseteq \{1, \dots, n\}$, $x$ a state and $t \in \mathbb{N}$. With $P_A$ the matrix $P$ with all rows and columns indexed by $A$ set to $0$, define

$$P_x(\tau_A > t) = \begin{cases} 0 & \text{if } x \in A, \\ \sum_{z} (P_A^{\,t})(x, z) & \text{if } x \notin A. \end{cases}$$

For a transition matrix $P$ this is the probability that the chain started at $x$ has $X_0, \dots, X_t$ all outside $A$, where $\tau_A = \min\{s \ge 0 : X_s \in A\}$.
