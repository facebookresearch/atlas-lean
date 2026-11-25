# Area under the queue-length curve over one signal cycle

For a signalized queue with arrival rate $\lambda$, discharge rate $\mu$, red time $R$ and green time $G$, whose length is $\lambda t$ for $t \le R$ and $\max\big(0, \lambda R - (\mu - \lambda)(t - R)\big)$ afterwards, assume $0 < \lambda < \mu$, $R \ge 0$, $G \ge 0$ and $\lambda (R + G) \le \mu G$ (the queue clears within the cycle). Then

$$\int_0^{R + G} Q(t)\,dt = \frac{\lambda R^2 \mu}{2(\mu - \lambda)}.$$
