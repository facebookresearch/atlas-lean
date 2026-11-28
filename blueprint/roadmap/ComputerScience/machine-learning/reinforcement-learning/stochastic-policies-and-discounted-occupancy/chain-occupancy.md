# Chain Occupancy

For a row-stochastic matrix $P$ on a finite set of states, a discount $0 \le \gamma < 1$, a weight function $\mu : S \to \mathbb R$ and a state $t$, the discounted occupancy of $t$ is

$$d_\mu(t) = (1 - \gamma) \sum_{s_0} \mu(s_0)\, V_t(s_0),$$

where $V_t$ is the value of the chain $P$ with reward $1$ at $t$ and $0$ elsewhere, the unique solution of $V = 1_t + \gamma P V$. The weights $\mu$ are arbitrary reals. When $\mu$ is an initial distribution, nonnegative with total mass $1$, $d_\mu(t)$ is the normalized discounted state occupancy $(1 - \gamma) \sum_n \gamma^n \Pr(S_n = t)$ of the chain started from $\mu$.
