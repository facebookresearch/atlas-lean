# Pi-regularity

A *single-flow packet sequence* $(A, L)$ consists of a wide-sense increasing sequence of packet dates $A = (A_1, A_2, \dots)$ and a sequence $L = (L_1, L_2, \dots)$ of positive integer packet lengths. A *regulation operator* $\Pi$ maps such sequences to sequences of time instants $\Pi(A, L)$ and satisfies:

1. (causality) $\Pi(A, L)_n$ depends only on $A_1, \dots, A_{n-1}$ and $L_1, \dots, L_n$;
2. (homogeneity) $\Pi(A + h, L) = \Pi(A, L) + h$ for every constant $h$;
3. (isotonicity) $A \le A'$ implies $\Pi(A, L) \le \Pi(A', L)$.

The flow $(A, L)$ is *$\Pi$-regular* if $A \ge \Pi(A, L)$. A *$\Pi$-regulator* is a system that is first in, first out for the flow and whose output is $\Pi$-regular. Arrival curve constraints are instances: a flow satisfies a wide-sense increasing [arrival curve](../arrival-curves.md) $\sigma$, for its cumulative function, exactly when $A_n - A_m \ge \sigma^\downarrow(L_m + \cdots + L_n)$ for all $m \le n$, with $\sigma^\downarrow$ the lower pseudo-inverse of $\sigma$, and this is $\Pi$-regularity for an operator built from $\sigma^\downarrow$. So are the length rate quotient constraint, $A_n \ge A_{n-1} + L_{n-1}/r$, and Chang's $g$-regularity. The maximum of two regulation operators is one, and a flow is regular for it exactly when it is regular for both.

## Depends on

- [Arrival curves](../arrival-curves.md)

## Sources

- J.-Y. Le Boudec, "A theory of traffic regulators for deterministic networks with application to interleaved regulators", *IEEE/ACM Transactions on Networking* 26(6):2721–2733, 2018; arXiv:1801.08477, <https://arxiv.org/abs/1801.08477>, Section II (notation, packet sequences), Section III.A (conditions C1–C4 and Definition 1), Section III.B (Chang's $g$-regularity), Section III.C, Theorem 1 and equation (25) (arrival curve constraints), the length rate quotient constraint of Section III, and equation (43) (combination of constraints).
