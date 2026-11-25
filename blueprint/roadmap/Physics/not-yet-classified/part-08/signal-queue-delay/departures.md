# Cumulative signal-queue departures

For arrival rate $\lambda$, service rate $\mu$ and red time $R$, the cumulative departures by time $s \ge 0$ are the arrivals minus the vehicles still queued, $\max(0, \lambda s - Q(s))$, where $Q$ is the queue length: $Q(s) = \lambda s$ for $s \le R$ and $Q(s) = \max(0, \lambda R - (\mu - \lambda)(s - R))$ for $s > R$.
