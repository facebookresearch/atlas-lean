# Long-run fraction of up time of an alternating renewal process

Let $(U_k, D_k)$, $k \ge 1$, be i.i.d. pairs of nonnegative random variables (within a pair, $U_k$ and $D_k$ may be dependent) with finite means $m_u = E[U_1]$, $m_d = E[D_1]$ and $m_u + m_d > 0$. A component is up on $[T_{k-1}, T_{k-1} + U_k)$ and down on $[T_{k-1} + U_k, T_k)$, where $T_0 = 0$ and $T_k = \sum_{i \le k}(U_i + D_i)$. Then the fraction of $[0, t]$ during which the component is up converges almost surely to $m_u/(m_u + m_d)$ as $t \to \infty$. For a two-state Markov component with failure rate $\lambda > 0$ and repair rate $\mu > 0$ started up, $U_k$ and $D_k$ are independent exponentials of rates $\lambda$ and $\mu$, and the limit is $\mu/(\lambda + \mu)$. If $\lambda = 0$, a component started up stays up and the fraction is $1$; if $\mu = 0 < \lambda$, it stays down after its first failure and the fraction tends to $0$.

Proof. Let $N(t) = \max\{k : T_k \le t\}$ and $R(t)$ the up time in $[0, t]$. By the strong law, $T_k/k \to m_u + m_d > 0$ and $\frac1k\sum_{i \le k}U_i \to m_u$ almost surely; so $T_k < \infty$ for all $k$, $N(t) \to \infty$, and $T_{N(t)} \le t < T_{N(t)+1}$ gives $N(t)/t \to 1/(m_u + m_d)$. Since $\sum_{i \le N(t)}U_i \le R(t) \le \sum_{i \le N(t)+1}U_i$, both bounds divided by $t$ tend to $m_u/(m_u + m_d)$.

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md): strong law of large numbers for i.i.d. integrable sequences.

## Background

- [Availability of a two-state repairable component](availability-of-a-two-state-repairable-component.md): the limiting probability of being up.
- [Long-run cost rate of an age-replacement policy](long-run-cost-of-age-replacement.md): renewal–reward for replacement policies.

## Sources

- K. Sigman, *Renewal theory, inspection paradox and renewal reward theorem* (lecture notes, IEOR 6711), Columbia University, 2009, Section 2, Theorem 2.1 (Renewal Reward Theorem), applied with reward R_j = U_j, <http://www.columbia.edu/~ks20/stochastic-I/stochastic-I-RRT.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
