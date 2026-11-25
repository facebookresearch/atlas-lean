# Shifting a sum over 1, …, n to start at 0

Let $M$ be an additive commutative monoid, let $f \colon \mathbb{N} \to M$ and let $n$ be a natural number. Then

$$\sum_{k=1}^{n} f(k) = \sum_{k=0}^{n-1} f(k+1),$$

both sides being empty sums, equal to $0$, when $n = 0$.

Equivalently, summing $f(c+1)$ over the $n$ elements $c=0,\ldots,n-1$ of $\mathrm{Fin}\,n$ gives the sum of $f$ over $1,\ldots,n$.
