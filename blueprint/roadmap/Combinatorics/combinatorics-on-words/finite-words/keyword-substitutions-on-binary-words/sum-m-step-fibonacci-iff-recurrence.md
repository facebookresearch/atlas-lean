# Recurrence for partial sums of $m$-step Fibonacci numbers

Let $m \ge 1$ and let
$F : \mathbb{N} \to \mathbb{N}$ satisfy $F(0) = 1$, $F(k) = 2^{k-1}$ for $1 \le k \le m - 1$,
and $F(k) = F(k-1) + \cdots + F(k-m)$ for $k \ge m$ (the $m$-step Fibonacci numbers). Then a
real sequence $(S_n)_{n \ge 0}$ satisfies $S_n = F(0) + F(1) + \cdots + F(n)$ for all $n$ if
and only if $S_n = 2^n$ for $0 \le n \le m$ and $S_n = 2 S_{n-1} - S_{n-m-1}$ for $n \ge m + 1$.

## Sources

- Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood, *A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.6.6, Lemma 9 (`jis-2025-25.6.6-lem-9`).
