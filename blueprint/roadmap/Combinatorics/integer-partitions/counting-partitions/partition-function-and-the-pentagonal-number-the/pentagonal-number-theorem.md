# Euler's pentagonal recurrence for the partition function

Let $p(n)$ be the number of
partitions of $n$, and for an integer $k$ let $g(k) = k(3k - 1)/2$ be the generalized pentagonal
number of $k$. For every natural number $n \ge 1$,
$p(n) = \sum_{k} (-1)^{k+1}\, p(n - g(k))$, where the sum runs over the nonzero integers $k$
with $g(k) \le n$.

## Sources

- https://en.wikipedia.org/wiki/Pentagonal_number_theorem ("Pentagonal number theorem").
