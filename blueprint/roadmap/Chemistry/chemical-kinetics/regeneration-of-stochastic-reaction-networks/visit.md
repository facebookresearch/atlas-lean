# The $k$-th visit to a state, counting from zero

Let $S$ be a set, $x_0, x \in S$, $k \in \mathbb{N}$ and $\omega$ a step sequence. The $k$-th visit
to $x_0$, counting from $0$, of the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
$Y$ started at $x$ is the step, in $\mathbb{N} \cup \{\infty\}$,

$$V_k(x_0, x, \omega) = \min\{\, n \in \mathbb{N} : Y_n(x, \omega) = x_0,\ N_n = k \,\} ,$$

where $N_n$ is the [number of visits](n-visits.md) to $x_0$ before step $n$ and the minimum of the
empty set is $\infty$. [At most one step](eq-of-visit.md) satisfies both conditions, so $V_k$ is
the step of the $(k+1)$-st visit to $x_0$.
