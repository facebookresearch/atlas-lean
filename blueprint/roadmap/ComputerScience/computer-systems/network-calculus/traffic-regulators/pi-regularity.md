# Pi-regularity

A *single-flow packet sequence* $(A, L)$ consists of a wide-sense increasing sequence of packet dates $A = (A_1, A_2, \dots)$ with $A_n \in [-\infty, +\infty)$ and a sequence $L = (L_1, L_2, \dots)$ of positive integer packet lengths. A *regulation operator* $\Pi$ maps such sequences to sequences $\Pi(A, L)$ in the same extended time domain $[-\infty, +\infty)$, not necessarily increasing, and satisfies:

1. (causality) $\Pi(A, L)_n$ depends only on $A_1, \dots, A_{n-1}$ and $L_1, \dots, L_n$;
2. (homogeneity) $\Pi(A + h, L) = \Pi(A, L) + h$ for every constant $h$;
3. (isotonicity) $A \le A'$ implies $\Pi(A, L) \le \Pi(A', L)$.

Causality and homogeneity force $\Pi(A, L)_1 = -\infty$: by causality $\Pi(A, L)_1$ does not depend on $A$, and by homogeneity it equals itself plus every real $h$; this is why the extended domain is needed. Physical packet sequences, whose delays are compared below, have real dates; the abstract input space also contains sequences such as $(-\infty, 0, 1, \dots)$.

The flow $(A, L)$ is *$\Pi$-regular* if $A \ge \Pi(A, L)$. A system is *first in, first out* for the flow if it maps $(A, L)$ to an output $(D, L)$ with $D$ wide-sense increasing, the packet numbering preserved, and $D \ge A$. A *$\Pi$-regulator* is a system that is first in, first out for the flow and whose output is $\Pi$-regular. Arrival curve constraints are instances: a flow with real packet dates $A_n \ge 0$ satisfies a wide-sense increasing [arrival curve](../arrival-curves.md) $\sigma$, for its left-continuous cumulative function $R(t) = \sum_n L_n \mathbf 1_{\{A_n < t\}}$ (which has $R(0) = 0$ because the dates are nonnegative), exactly when $A_n - A_m \ge \sigma^\downarrow(L_m + \cdots + L_n)$ for all $m \le n$, with $\sigma^\downarrow$ the lower pseudo-inverse of $\sigma$. The pairs $m < n$ are $\Pi$-regularity for the operator $\Pi(A, L)_n = \max_{1 \le m \le n - 1}\{A_m + \sigma^\downarrow(L_m + \cdots + L_n)\}$ (the maximum of the empty set being $-\infty$), which takes values in $[-\infty, +\infty)$ when $\sigma$ is unbounded, so that $\sigma^\downarrow$ is finite; the diagonal pairs $m = n$ add the conditions $\sigma^\downarrow(L_n) = 0$, which the operator does not see. So the arrival curve constraint is $\Pi$-regularity for this operator exactly when $\sigma^\downarrow(L_n) = 0$ for every $n$. For unit packets with $A_n = 3n$ and $\sigma(t) = t$ every pair $m < n$ holds, since $3(n - m) \ge n - m + 1$, but the diagonal requires $0 \ge 1$. So are the length rate quotient constraint, $A_n \ge A_{n-1} + L_{n-1}/r$, and Chang's $g$-regularity. The maximum of two regulation operators is one, and a flow is regular for it exactly when it is regular for both.

## Depends on

- [Arrival curves](../arrival-curves.md)

## Sources

- J.-Y. Le Boudec, "A theory of traffic regulators for deterministic networks with application to interleaved regulators", *IEEE/ACM Transactions on Networking* 26(6):2721–2733, 2018; arXiv:1801.08477, <https://arxiv.org/abs/1801.08477>; section, theorem and equation numbers are those of the arXiv version, Section II (notation, packet sequences), Section III.A (conditions C1–C4 and Definition 1), Section III.B (Chang's $g$-regularity), Section III.C, Theorem 1 and equation (25) (arrival curve constraints), the length rate quotient constraint of Section III, and equation (43) (combination of constraints).
