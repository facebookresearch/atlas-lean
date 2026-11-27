# Sum mul chain Value

For a row-stochastic matrix $P$, a discount $0 \le \gamma < 1$, weights $\mu : S \to \mathbb R$ and a state reward $f : S \to \mathbb R$,

$$\sum_{s_0} \mu(s_0)\, V_f(s_0) = (1 - \gamma)^{-1} \sum_t d_\mu(t)\, f(t),$$

where $V_f$ is the value of the chain $P$ with reward $f$ and $d_\mu$ is the discounted occupancy of the weights $\mu$. The identity is algebraic and holds for any real weights. When $\mu$ is an initial distribution (nonnegative, with total mass $1$), it says that the expected value of $f$ from $\mu$ is $(1 - \gamma)^{-1}$ times the expected reward under the occupancy distribution.
