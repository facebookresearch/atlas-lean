# Inside recursion

Fix a sequence $s$, a complementarity relation, a minimum hairpin size $m$ and weights $w(i, j)$ in a commutative semiring. The inside value $Z(i, n)$ of the interval of length $n$ starting at $i$, i.e. of the positions $i, \dots, i + n - 1$, is defined by recursion on $n$: $Z(i, 0) = 1$, and for $n \ge 1$

$$Z(i, n) = Z(i + 1, n - 1) + \sum_{k=m}^{n-2} [\,i \text{ and } i + 1 + k \text{ can pair}\,]\; w(i, i + 1 + k)\, Z(i + 1, k)\, Z(i + k + 2, n - 2 - k),$$

where the sum is empty when $n - 2 < m$ and [can pair](can-pair.md) is as defined: base $i$ is either unpaired, or paired with $i + 1 + k$, which encloses the interval $i + 1, \dots, i + k$ and leaves the outer interval $i + k + 2, \dots, i + n - 1$.
