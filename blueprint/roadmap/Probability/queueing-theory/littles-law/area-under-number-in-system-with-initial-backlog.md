# Area under the number-in-system path with an initial backlog

Let finitely many customers have arrival times $a_i \in \mathbb{R}$ and departure times $d_i \ge a_i$; arrivals before time $0$ are allowed, so customers already present at time $0$ are included. Let $N(t) = \#\{i : a_i \le t < d_i\}$. Then for every $T \ge 0$ (including $T = 0$),

$$
\int_0^T N(t)\,dt = \sum_i \max\bigl(0,\ \min(d_i, T) - \max(a_i, 0)\bigr),
$$

since customer $i$ contributes the length of $[a_i, d_i) \cap [0, T]$. When every $a_i \ge 0$ the right side is $\sum_{i : a_i \le T} \min(d_i - a_i, T - a_i)$, the identity of the area page. Proof: exchange the finite sum with the integral and integrate each interval indicator. A Little's-law limit for a system that starts with customers present needs its own hypotheses on the initial population and is not part of this statement.

## Proof depends on

- [Area under the number-in-system path](area-under-number-in-system.md): the case of nonnegative arrival times, whose proof (exchange of the finite sum and integral of an interval indicator) is the same.

## Background

- [Little's law](littles-law.md): the limit theorem for nonnegative arrival times, which this finite identity does not extend.

## Sources

- K. Sigman, *Notes on Little's law*, lecture notes, Columbia University, 2009, <http://www.columbia.edu/~ks20/stochastic-I/stochastic-I-LL.pdf>, equations (7)–(12) (nonnegative arrival times)
