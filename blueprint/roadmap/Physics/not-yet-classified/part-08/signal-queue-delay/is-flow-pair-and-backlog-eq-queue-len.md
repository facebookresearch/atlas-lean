# Signal queue as a cumulative flow pair

Let $0 < \lambda < \mu$ and $R \ge 0$, and let the queue length be $\ell(t) = \lambda t$ for $t \le R$ and $\ell(t) = \max(0, \lambda R - (\mu - \lambda)(t - R))$ for $t > R$. Let cumulative arrivals be $A(s) = \lambda s$ and cumulative departures $D(s) = \lambda s - \ell(s)$ for $s \ge 0$. Then $(A, D)$ is a lossless flow pair: both vanish at time $0$, both are nondecreasing, and $D \le A$. Moreover the backlog $A(s) - D(s)$ equals $\ell(s)$ for every $s \ge 0$.
