# Lindley's recursion and the maximum of the random walk

Let $X_1, X_2, \dots$ be real numbers and define $W_0 = 0$, $W_n = \max(0, W_{n-1} + X_n)$; for the single-server first-come first-served queue with service times $B_n$ and interarrival times $A_{n+1}$, the waiting times satisfy this recursion with $X_n = B_{n-1} - A_n$. By Lindley duality, $W_n = \max_{0 \le k \le n}(s_n - s_k)$ with $s_k = X_1 + \dots + X_k$, the walk maximum of the reversed list $X_n, \dots, X_1$. If the $X_i$ are i.i.d., $W_n$ has the law of $M_n = \max_{0 \le k \le n} S_k$ for the random walk $S_k = X_1 + \dots + X_k$. Since $M_n$ increases to $M_\infty = \sup_{k \ge 0} S_k \in [0, \infty]$, $P(W_n \le x) \to P(M_\infty \le x)$ for every real $x$: when $M_\infty$ is almost surely finite this is convergence in distribution of $W_n$ to $M_\infty$, and otherwise mass escapes to $+\infty$ and $W_n$ has no limit law on $\mathbb{R}$. $M_\infty$ is almost surely finite exactly when $X_1 = 0$ almost surely (then $M_\infty = 0$) or $S_k \to -\infty$ almost surely; the latter holds when $E|X_1| < \infty$ and $E[X_1] < 0$, that is $E[B] < E[A]$ for integrable service and interarrival times. The stationary-workload construction of Loynes for stationary ergodic inputs and the Pollaczek–Khinchine formula $E[W_\infty] = \lambda E[B^2]/(2(1-\rho))$ for Poisson arrivals with $\rho = \lambda E[B] < 1$ and $E[B^2] < \infty$ are separate statements.

## Proof depends on

- [Lindley duality](../../random-walks/maximal-segment-score-of-a-random-sequence/lindley-eq-walk-max-reverse.md): the finite identity for $W_n$.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Reversal of i.i.d. increments preserves the joint law of the partial sums.
- A random walk whose i.i.d. increments are not almost surely zero either drifts to $-\infty$ almost surely or has an almost surely infinite supremum.

## Background

- [Reversing the score sequence does not change the weighted average](../../random-walks/maximal-segment-score-of-a-random-sequence/score-expect-reverse.md): reversal of an i.i.d. sequence on a finite alphabet preserves its law.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, §7.5 (equation (7.10))
- O. Boxma, O. Kella and M. Mandjes, "On fluctuation-theoretic decompositions via Lindley-type recursions", arXiv:2212.01811, 2022, <https://arxiv.org/abs/2212.01811>, equations (15)–(16) and Remark 4
