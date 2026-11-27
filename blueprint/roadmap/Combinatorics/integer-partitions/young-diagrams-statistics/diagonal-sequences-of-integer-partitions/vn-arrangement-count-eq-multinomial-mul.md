# Counting $k$-vn-arrangements of a multiset

Let $k \le t$ be natural numbers, let
$b_0, b_1, \dots$ be natural numbers, and let $M$ be the multiset of integers containing $b_i$
copies of $i$ for each $0 \le i \le t$, so that $M$ has $m = b_0 + \dots + b_t$ elements. Then
the number of $k$-vn-arrangements of $M$, that is, orderings $(v_1, \dots, v_m)$ of $M$ with
$v_{j+1} - v_j \le k$ for all $j$, is

$$
\binom{b_0 + \dots + b_k}{b_0, \dots, b_k} \prod_{i=1}^{t-k} \binom{b_i + \dots + b_{i+k}}{b_{i+k}}
$$

## Sources

- Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*, INTEGERS 25 (2025), Article A60, Proposition 7.
