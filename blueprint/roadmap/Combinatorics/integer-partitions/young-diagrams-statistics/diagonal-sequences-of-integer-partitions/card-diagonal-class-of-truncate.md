# Truncating the staircase of a diagonal sequence

For $m \ge 0$ and a sequence
$s = (s_1, s_2, \dots)$ of natural numbers, let $d(m, s)$ be the sequence
$(1, 2, \dots, m, m^{(s_m)}, (m-1)^{(s_{m-1})}, \dots, 1^{(s_1)})$ followed by zeros, where
$v^{(r)}$ means $r$ copies of $v$, and let $n(m, s) = m(m+1)/2 + \sum_{j=1}^{m} j s_j$. Let
$1 \le k < q$ with $s_k \ge 2$ and $s_j = 0$ for all $k < j \le q$. Then the number of partitions
of $n(q, s)$ with diagonal sequence $d(q, s)$ equals the number of partitions of $n(k, s)$ with
diagonal sequence $d(k, s)$.

## Sources

- Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*, INTEGERS 25 (2025), Article A60, Corollary 6 (4).
