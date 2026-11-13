# Generating function of smooth words ending in their largest letter

For $i \ge 1$, let
$s(n, i; q)$ be the capacity distribution of the smooth words of length $n$ that end in $i$ and
have largest letter $i$, and let $t(m, j; q)$ be the area distribution (the area of a word is the
sum of its letters) of the words of length $m$ over $\{1, \dots, j\}$ that begin and end with $j$
and whose adjacent letters differ by at most $1$. In the ring of formal power series in $x$ over
the Laurent polynomials $\mathbb{Z}[q, q^{-1}]$,

$$
\sum_{n \ge 0} s(n, i; q)\, x^n = x^i \prod_{j=0}^{i-1}
\Bigl(1 - x - x \sum_{m \ge 0} q^{(j+1)m}\, t(m, j; 1/q)\, x^m\Bigr)^{-1}.
$$

The factor for $j = 0$ is $(1 - x)^{-1}$, since $t(m, 0; q) = 0$ for every $m$.

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 9.
