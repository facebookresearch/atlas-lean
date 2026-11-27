# Signal queue length

For arrival rate $\lambda$, service rate $\mu$ and red duration $R$, the queue length at time $t$ is $\lambda t$ for $t \le R$ and $\max\big(0, \lambda R - (\mu - \lambda)(t - R)\big)$ for $t > R$. For $0 < \lambda < \mu$ and $R \ge 0$ this is a queue that grows at rate $\lambda$ during red, then drains at rate $\mu - \lambda$ until it clears and stays at zero.
