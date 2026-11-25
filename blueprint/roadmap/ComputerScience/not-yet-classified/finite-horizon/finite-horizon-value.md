# Finite-horizon value

For a Markov decision process with finitely many states, a finite nonempty set of actions, rewards $r(s, a)$, transition probabilities $P(s, a, s')$ and discount $\gamma$, the $k$-step finite-horizon value is defined by $V_0 = 0$ and
$$V_{k+1}(s) = \max_a \Big( r(s, a) + \gamma \sum_{s'} P(s, a, s')\, V_k(s') \Big).$$
