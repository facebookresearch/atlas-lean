# Carry-less multiplication by Four-Russians tables

Let polynomials over $\mathbb{F}_2$ of degree below $q$ be stored as $q$-bit words and split into chunks of $b$ bits. With a precomputed table of all carry-less products of two $b$-bit chunks ($2^{2b}$ entries of $2b$ bits), the carry-less product of two $q$-bit polynomials is computed with $\lceil q/b \rceil^2$ table lookups, shifts and exclusive ors, and reduction modulo a trinomial $x^{q} + x^{q/2} + 1$ takes $O(q / b)$ further word operations per word of the product. Choosing $b \approx \frac13 \log_2 n$ keeps the table at $O(n^{2/3})$ entries, so evaluating a degree-$(k-1)$ polynomial hash over $\mathbb{F}_{2^q}$ costs $O(k (q/b)^2)$ instructions.

## Proof sketch

Carry-less multiplication is bilinear over $\mathbb{F}_2$, so the product is the exclusive or of the shifted chunk products. Reduction by a trinomial replaces each high monomial $x^{q + i}$ by $x^{q/2 + i} + x^i$, which is two shifted exclusive ors of the high part, applied twice.

## Depends on

- [The trinomials x^(2·3^t) + x^(3^t) + 1 are irreducible over GF(2)](irreducible-trinomials-over-gf2.md)

## Sources

- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1-3), 2012.
- R. Lidl and H. Niederreiter, "Finite Fields", 2nd edition, Cambridge University Press, 1997.
