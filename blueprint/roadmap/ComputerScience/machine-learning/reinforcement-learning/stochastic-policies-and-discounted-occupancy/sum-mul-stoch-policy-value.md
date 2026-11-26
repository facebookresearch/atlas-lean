# Sum mul stoch Policy Value

For a finite MDP with stochastic transitions, a discount $0 \le \gamma < 1$, a stochastic policy $\pi$ (a row-stochastic matrix of action weights $\pi(s, a)$) and weights $\mu : S \to \mathbb R$,

$$\sum_s \mu(s)\, V^\pi(s) = (1 - \gamma)^{-1} \sum_{(s, a)} d^\pi_\mu(s, a)\, r(s, a),$$

where $V^\pi$ is the discounted value of $\pi$, $r$ is the reward, and $d^\pi_\mu(s, a)$ is the discounted state-action occupancy of $\pi$ from $\mu$: the discounted state occupancy of the chain of states under $\pi$, from the weights $\mu$, times $\pi(s, a)$. The identity holds for any real weights. When $\mu$ is an initial distribution (nonnegative, with total mass $1$), it says that the expected value of $\pi$ is $(1 - \gamma)^{-1}$ times the expected reward under its occupancy distribution.
