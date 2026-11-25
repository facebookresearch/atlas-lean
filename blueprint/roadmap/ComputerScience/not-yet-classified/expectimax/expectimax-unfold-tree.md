# Expectimax of the MDP unfolding is the finite-horizon value

For an MDP with finite state and action sets (actions nonempty), real rewards and transition weights, a discount $\gamma \in \mathbb R$, a depth $k$ and a state $s$, the expectimax value of the depth-$k$ max/chance unfolding at $s$ equals the $k$-step finite-horizon value $V_k(s)$, where $V_0 = 0$ and $V_{k+1}(s) = \max_a \big(r(s, a) + \gamma \sum_{s'} P(s' \mid s, a) V_k(s')\big)$. The identity is algebraic and needs no stochasticity or discount condition.
