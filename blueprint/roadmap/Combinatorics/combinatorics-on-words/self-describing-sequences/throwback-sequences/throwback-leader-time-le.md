# Recursive bound on the time to become leader

Let $X = (x_0, x_1, \dots)$ be a sequence
of pairwise distinct positive integers, with positions numbered from $0$, the leader being at
position $0$. Let $\tau$ be the throwback and $T(X) = (t_0, t_1, \dots)$ the throwback
sequence, so $t_k$ is the leader of $\tau^k(X)$. Let $n \ge 1$, and let $N$ be the number of
indices $i$ with $x_i < n$. Suppose $a$ and $b$ are natural numbers such that for every
$m \ge 0$, the term at position $n - 1$ of $\tau^m(X)$ equals $t_{m+k}$ for some $k \le a$, and
the term at position $N$ of $\tau^m(X)$ equals $t_{m+k}$ for some $k \le b$. Then for every
$m \ge 0$, the term at position $n$ of $\tau^m(X)$ equals $t_{m+k}$ for some $k \le a + b + 1$.

This is the bound $M(n) \le M(n - 1) + M(N) + 1$ of the source, stated for upper bounds, where
$M(n)$ is the largest number of throwbacks the term at position $n$ of any $\tau^m(X)$ needs to
become leader.

## Sources

- Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*, Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 3 (`jis-2025-25.5.1-lem-3`).
