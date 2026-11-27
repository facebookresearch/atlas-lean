# Levels hold interval minima

Let $a = (a_0, \dots, a_{n-1})$ be a list over a linearly
ordered type, and let $k$ and $i$ be natural numbers with $i + 2^k \le n$. Then level $k$ of $a$
has an element at index $i$, and it equals $\min(a_i, a_{i+1}, \dots, a_{i+2^k-1})$.
