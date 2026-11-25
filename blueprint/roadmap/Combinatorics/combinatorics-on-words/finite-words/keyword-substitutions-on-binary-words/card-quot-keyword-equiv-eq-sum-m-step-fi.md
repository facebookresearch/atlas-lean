# Keyword classes are counted by partial sums of $m$-step Fibonacci numbers

Let
$m, n \ge 1$ and let $F_0, F_1, F_2, \dots$ be the $m$-step Fibonacci numbers: $F_0 = 1$,
$F_k = 2^{k-1}$ for $1 \le k \le m - 1$, and $F_k = F_{k-1} + F_{k-2} + \dots + F_{k-m}$ for
$k \ge m$. Then for every binary keyword $a$ of length $m + 1$, the number of equivalence
classes of the relation $\sim_a$ on binary words of length $n$ is $F_0 + F_1 + \dots + F_n$.

## Sources

- Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood, *A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.6.6, Theorem 1 (`jis-2025-25.6.6-thm-1`).
