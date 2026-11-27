# Recurrence for the capacity distribution of smooth words ending in their largest letter

Let $s(n, i; q)$ be the capacity distribution of the smooth words of length $n$ that end in $i$ and
have largest letter $i$, and let $t(m, j; q)$ be the area distribution (the area of a word is the
sum of its letters) of the words of length $m$ over $\{1, \dots, j\}$ that begin and end with $j$
and whose adjacent letters differ by at most $1$. For $1 < i < n$, in the ring
$\mathbb{Z}[q, q^{-1}]$ of Laurent polynomials,

$$
s(n, i; q) = s(n - 1, i; q) + s(n - 1, i - 1; q) +
\sum_{m=1}^{n-i-1} q^{mi}\, s(n - m - 1, i; q)\, t(m, i - 1; 1/q).
$$

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 7.
