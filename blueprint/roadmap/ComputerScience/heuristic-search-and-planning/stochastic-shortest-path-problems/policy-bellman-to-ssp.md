# The undiscounted Bellman operator of the SSP is the discounted one

For a Markov decision process $M$ with finitely many states, a discount factor $\gamma$ and a deterministic stationary policy $\mu$, the undiscounted Bellman operator of $\mu$ in the [associated SSP](to-ssp.md) equals the $\gamma$-discounted Bellman operator of $\mu$ in $M$:

$$r(s,\mu(s)) + \sum_{s'} \gamma\, p(s,\mu(s),s')\, V(s') = r(s,\mu(s)) + \gamma \sum_{s'} p(s,\mu(s),s')\, V(s').$$
