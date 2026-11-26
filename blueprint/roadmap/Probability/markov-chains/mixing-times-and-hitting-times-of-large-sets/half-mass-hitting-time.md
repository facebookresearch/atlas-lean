# Half-mass hitting time of a Markov chain

Let $n \in \mathbb{N}$, let $P$ be a real $n \times n$ matrix and $\pi : \{1, \dots, n\} \to \mathbb{R}$. The half-mass hitting time is

$$T(1/2) = \sup\Big\{h_A(x) : x \text{ a state},\ A \subseteq \{1, \dots, n\},\ \pi(A) = \sum_{y \in A} \pi(y) \ge \tfrac12\Big\} \in [0, \infty],$$

where $h_A(x) = \sum_{t \ge 0} \max\big(P_x(\tau_A > t), 0\big)$ is the [hitting-time sum](expected-hitting-time.md): the positive part of each survival term is taken before summing, in the extended nonnegative reals. When $P$ is a transition matrix the survival terms are probabilities, $h_A(x)$ is the expected hitting time $\mathbb{E}_x[\tau_A]$ of $A$ from $x$, and $T(1/2)$ is the largest expected time to reach a set of $\pi$-mass at least $1/2$. The supremum of the empty family is $0$.
