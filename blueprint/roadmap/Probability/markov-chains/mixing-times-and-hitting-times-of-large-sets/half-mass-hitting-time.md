# Half-mass hitting time of a Markov chain

Let $n \in \mathbb{N}$, let $P$ be a real $n \times n$ matrix and $\pi : \{1, \dots, n\} \to \mathbb{R}$. The half-mass hitting time is

$$T(1/2) = \sup\Big\{\mathbb{E}_x[\tau_A] : x \text{ a state},\ A \subseteq \{1, \dots, n\},\ \pi(A) = \sum_{y \in A} \pi(y) \ge \tfrac12\Big\} \in [0, \infty],$$

where $\mathbb{E}_x[\tau_A] = \sum_{t \ge 0} P_x(\tau_A > t)$ is the expected hitting time of $A$ from $x$, valued in $[0, \infty]$. The supremum of the empty family is $0$.
