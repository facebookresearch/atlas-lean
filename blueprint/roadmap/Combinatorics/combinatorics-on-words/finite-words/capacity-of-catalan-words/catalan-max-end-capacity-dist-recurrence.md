# Recurrence for the capacity of Catalan words ending in their largest letter

For natural
numbers $n$ and $i$, let $b(n, i; q)$ be the capacity distribution of the Catalan words of length
$n$ that end in $i$ and have all letters at most $i$. For natural numbers $m$ and $k$, let
$c(m, k; q) \in \mathbb{Z}[q]$ be the area distribution of the words of length $m$ with letters
in $\{1, \dots, k\}$, each letter at most one more than the letter before it, and last letter
$k$, and let $c(m, k; 1/q)$ be its image under $q \mapsto q^{-1}$. For all natural numbers $n$
and $i$ with $1 < i < n$, in $\mathbb{Z}[q, q^{-1}]$,

$$b(n, i; q) = b(n-1, i; q) + b(n-1, i-1; q) +
\sum_{m=1}^{n-i-1} q^{mi}\, b(n-m-1, i; q)\, c(m, i-1; 1/q).$$

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 2 (`integers-2025-A5-lem-2`).
