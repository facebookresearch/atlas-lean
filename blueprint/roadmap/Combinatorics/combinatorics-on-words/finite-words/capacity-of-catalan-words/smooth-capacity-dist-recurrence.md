# Recurrence for the capacity distribution of smooth words by last letter

Let $r(n, i; q)$
be the capacity distribution of the smooth words of length $n$ ending in $i$, let $s(n, i; q)$ be
that of those smooth words of length $n$ ending in $i$ whose largest letter is $i$, and let
$t(m, j; q)$ be the area distribution (the area of a word is the sum of its letters) of the words
of length $m$ over $\{1, \dots, j\}$ that begin and end with $j$ and whose adjacent letters
differ by at most $1$. For $1 < i < n$, in the ring $\mathbb{Z}[q, q^{-1}]$ of Laurent
polynomials,

$$
r(n, i; q) = r(n - 1, i; q) + r(n - 1, i + 1; q) + s(n - 1, i - 1; q) +
\sum_{m=1}^{n-i-1} q^{mi}\, r(n - m - 1, i; q)\, t(m, i - 1; 1/q).
$$

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 7.
