# First-jump decomposition

Let $Q$ be a real square matrix indexed by a set $S$, $i \in S$, $\omega = ((\xi_n, E_n))_n$ a step
sequence and $t \ge 0$. With $S_0 = S_0(i, \omega)$ the first [holding time](ctmc-holding-time.md)
and $X$ the [path](ctmc-path.md),

$$X_t(i, \omega) = \begin{cases} i & \text{if } t < S_0, \\ X_{t - S_0}\bigl(\xi_0(i), \theta_1 \omega\bigr) & \text{otherwise,} \end{cases}$$

where $\theta_1 \omega$ is the [shifted step sequence](ctmc-shift.md) and $t - S_0$ is read as $0$
if negative (here $S_0$ is finite when $t \ge S_0$).
