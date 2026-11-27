# Kingman's bound for the GI/G/1 queue

In the GI/G/1 queue let the interarrival times $U$ and service times $V$ be independent i.i.d. sequences with finite second moments and $E[V] < E[U]$, and let $W$ be the stationary waiting time, the [stationary law of Lindley's recursion](stationary-law-of-the-lindley-recursion.md) $W_{n+1} = \max(0, W_n + V_n - U_{n+1})$. Then

$$
E[W] \le \frac{\operatorname{Var}(U) + \operatorname{Var}(V)}{2\,(E[U] - E[V])} .
$$

When $E[V] > 0$, with $E[U] = 1$, $0 < \rho = E[V] < 1$ and squared coefficients of variation $c_a^2$ and $c_s^2$ of $U$ and $V$, this reads $E[W] \le \rho^2(c_a^2/\rho^2 + c_s^2)/(2(1 - \rho))$. For deterministic arrivals ($c_a^2 = 0$) the bound is approached by two-point service laws with mean $\rho$ and squared coefficient of variation $c_s^2$ whose upper point tends to infinity. No heavy-traffic exactness holds without a specified family of queues: for $\rho = 1 - 1/n$, deterministic service $V = \rho$ and interarrivals equal to $1 + n$ with probability $1/(n^2 + 1)$ and to $\rho$ otherwise, $E[U] = 1$ and $\operatorname{Var}(U) = 1$, but no customer ever waits, while the bound is $n/2$.

**Proof.** Write $X = V - U$, independent of $W$, and $W' = \max(0, W + X)$, $I = W' - (W + X) = \max(0, -(W + X)) \ge 0$, so $W' I = 0$. Stationarity gives $E[W'] = E[W]$ and $E[W'^2] = E[W^2]$, hence $E[I] = -E[X]$ and, squaring $W' - I = W + X$, $E[I^2] = 2E[W]E[X] + E[X^2]$. Since $E[I^2] \ge E[I]^2 = E[X]^2$, this gives $-2E[W]E[X] \le \operatorname{Var}(X) = \operatorname{Var}(U) + \operatorname{Var}(V)$. (This step uses $E[W^2] < \infty$, which holds when $E[V^3] < \infty$ but can fail when only $E[V^2] < \infty$; Kingman's argument avoids it by truncation.)

## Depends on

- [The supremum of the random walk is a stationary law of Lindley's recursion](stationary-law-of-the-lindley-recursion.md)

## Expansion

This page becomes ready once this prerequisite is stated: finiteness of $E[W^2]$, or a truncation argument replacing it, for the stationary waiting time when the service times have a finite second moment only (the proof above uses $E[W^2] < \infty$; in general it needs a finite third moment of $V$).

## Sources

- Y. Chen and W. Whitt, "Algorithms for the upper bound mean waiting time in the GI/GI/1 queue", *Queueing Systems*, 2020, <https://doi.org/10.1007/s11134-020-09649-9>, Section 2.2, equation (2.6) (the Kingman upper bound), and definition (2.10) with Corollary 5.2 (tightness of Kingman's bound for deterministic arrivals as the upper point of the two-point service law tends to infinity).
- J. F. C. Kingman, "Some inequalities for the queue GI/G/1", *Biometrika* 49(3–4):315–324, 1962, where the bound is proved.
