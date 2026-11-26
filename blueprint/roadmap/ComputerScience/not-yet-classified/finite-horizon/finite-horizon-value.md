# Finite-horizon value

For a Markov decision process with finitely many states, a finite nonempty set of actions, real rewards $r(s, a)$, real transition weights $P(s, a, s')$ and a real discount $\gamma$, the $k$-step finite-horizon value is defined by $V_0 = 0$ and

$$V_{k+1}(s) = \max_a \Big( r(s, a) + \gamma \sum_{s'} P(s, a, s')\, V_k(s') \Big).$$

The weights are not required to be nonnegative or to sum to $1$; when the process is stochastic ($P(s, a, \cdot)$ is a probability distribution for every $s$ and $a$), $V_k(s)$ is the optimal expected discounted return over $k$ steps from $s$.
