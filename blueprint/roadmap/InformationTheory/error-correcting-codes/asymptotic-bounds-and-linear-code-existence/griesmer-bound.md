# The Griesmer bound for linear codes

Let $C$ be a linear code of length $n$ and dimension $k$ over a finite field with $q$ elements, with minimum distance at least $d \ge 1$. Then

$$\sum_{i=0}^{k-1} \Bigl\lceil \frac{d}{q^i} \Bigr\rceil \le n.$$

Since the sum is at least $d + k - 1$, this refines the Singleton bound $k + d \le n + 1$ for linear codes. The key step uses the residual code of a codeword $c$: the puncturing of $C$ to the $n - \mathrm{wt}(c)$ coordinates where $c$ vanishes, whose nonzero words have weight at least $\lceil (q d - (q - 1)\mathrm{wt}(c))/q \rceil$, and whose dimension is $k - 1$ when $0 < (q - 1)\mathrm{wt}(c) < q d$.

## Proof sketch

Summing the weights of the $q$ translates $x - a c$ over $a \in \mathbb{F}_q$ gives $q\,\mathrm{wt}(x|_{c = 0}) + (q - 1)\mathrm{wt}(c)$, and when $x|_{c = 0} \ne 0$ we have $x \notin \mathrm{span}(c)$, so all $q$ translates are nonzero codewords of weight at least $d$; this bounds the residual distance. Taking $c$ of minimum weight $d$, the residual code has length $n - d$, dimension $k - 1$ and distance at least $\lceil d/q \rceil$, and induction on $k$ gives the sum.

## Depends on

- [Linear code](../linear-codes/linear-code.md)
- [Minimum distance](../linear-codes/min-dist.md)

## Proof depends on

- [Singleton bound](../bounds-on-code-size/singleton-bound.md)

## Sources

- J. H. Griesmer, "A Bound for Error-Correcting Codes", IBM Journal of Research and Development, 1960.
- F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes", North-Holland, 1977.
