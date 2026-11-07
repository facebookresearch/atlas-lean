# The Fibonacci numbers are the only Zeckendorf fundamental sequence

Let
$H \colon \mathbb{N} \to \mathbb{N}$ be a strictly increasing sequence of positive integers, and
call a finite set $s \subseteq \mathbb{N}$ nonadjacent if $k \in s$ implies $k + 1 \notin s$.
Then every natural number (including $0$) equals $\sum_{k \in s} H_k$ for exactly one nonadjacent
finite set $s$ if and only if $H_k = F_{k+2}$ for all $k$, where $F_0 = 0$, $F_1 = 1$ and
$F_{n+2} = F_{n+1} + F_n$ are the Fibonacci numbers.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Lemma 1 (`integers-2025-A25-lem-1`).
