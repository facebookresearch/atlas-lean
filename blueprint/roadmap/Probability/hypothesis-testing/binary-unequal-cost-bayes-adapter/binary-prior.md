# Binary Prior

For real numbers $\pi_0, \pi_1$, the binary prior on the truth $\{0, 1\}$ (false $= 0$, true $= 1$) is the measure

$$\max(\pi_0, 0)\, \delta_0 + \max(\pi_1, 0)\, \delta_1,$$

so negative weights are replaced by $0$. It is not normalized unless $\pi_0, \pi_1 \ge 0$ and $\pi_0 + \pi_1 = 1$.
