# The SiPhy constraint-vector update

Let $I$ be a nonempty finite state set, $n$ a real matrix, $\tau, r$ real functions, $\omega$ real and $R$ a real matrix such that $c_b > 0$ and $\omega e_b \ge 0$ for every $b$, where $c$ are the [state weights](in-count.md) and $e$ the [exchange rates](exit-weight.md). The constraint-vector update is

$$\hat\pi_b = \frac{c_b}{\omega e_b + \gamma},$$

where $\gamma$ is the unique [Lagrange multiplier](exists-unique-lagrange.md) for $c$ and $d = \omega e$.
