# Simplex codes: parameters and equality in the Griesmer bound

Let $\mathbb{F}$ be a finite field with $q$ elements and $k \ge 1$. Choose one nonzero representative $p$ of each one-dimensional subspace of $\mathbb{F}^k$ (there are $(q^k - 1)/(q - 1)$ of them). The $q$-ary simplex code is the image of the injective linear map $x \mapsto (\langle x, p \rangle)_p$. It has dimension $k$, every nonzero codeword has weight exactly $q^{k-1}$, so its minimum distance is $q^{k-1}$, and it meets the Griesmer bound with equality:

$$\sum_{i=0}^{k-1} \Bigl\lceil \frac{q^{k-1}}{q^i} \Bigr\rceil = \frac{q^k - 1}{q - 1}.$$

## Proof sketch

For $x \ne 0$, the representatives $p$ with $\langle x, p\rangle = 0$ are those of the lines in the hyperplane $x^\perp$, of which there are $(q^{k-1} - 1)/(q - 1)$; the remaining $q^{k-1}$ points give nonzero coordinates. The Griesmer sum is a geometric series equal to the length.

## Depends on

- [Linear code](../linear-codes/linear-code.md)
- [Minimum distance](../linear-codes/min-dist.md)
- [The Griesmer bound for linear codes](griesmer-bound.md)

## Sources

- F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes", North-Holland, 1977.
- J. H. Griesmer, "A Bound for Error-Correcting Codes", IBM Journal of Research and Development, 1960.
