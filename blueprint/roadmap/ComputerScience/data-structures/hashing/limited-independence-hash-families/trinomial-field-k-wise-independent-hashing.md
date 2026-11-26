# Exact k-wise independence over explicit trinomial binary fields and universe reduction

For $t \ge 0$ the polynomial $X^{2\cdot 3^t} + X^{3^t} + 1$ is irreducible over $\mathbb{F}_2$, giving an explicit field $K_t$ with $2^{2\cdot 3^t}$ elements whose elements are bit strings of length $2\cdot 3^t$. If $U \le 2^{2\cdot 3^t}$ and $M \le 2\cdot 3^t$, then evaluating a uniformly random polynomial of degree less than $k$ over $K_t$ at (the embedding of) a key in $\{0, \dots, U-1\}$ and keeping the low $M$ coordinates of the result is an exactly $k$-wise independent family from $\{0, \dots, U-1\}$ onto $\{0,1\}^M$, with no modulo bias; $t$ can be chosen with $2\cdot 3^t \le 3\max(\lceil \log_2 U \rceil, M)$.

Composing with a multiply-shift universe reduction to $\min(w_0, 3b)$ bits gives a two-stage family that is exactly $k$-wise independent on every key set $S$ on which the reduction is injective, and the reduction fails to be injective on $S$ with probability at most $\binom{|S|}{2} \cdot 2/2^{3b}$ when $3b \le w_0$ (and never when $w_0 < 3b$).

## Proof sketch

Polynomial evaluation over $K_t$ is $k$-wise independent onto $K_t$. The coordinate map $K_t \to \{0,1\}^{2\cdot 3^t}$ and the projection to $M$ bits are surjective $\mathbb{F}_2$-linear maps, so every output pattern has the same number of preimages and uniformity survives. For the composition, injectivity on $S$ makes distinct keys distinct field points; a union bound with multiply-shift universality bounds the failure probability.

## Depends on

- [Polynomials of degree below k form a k-wise independent family](polynomial-k-wise-independent-hashing.md)
- [Multiply-shift is 2/2^M-universal](../word-ram-hash-families/multiply-shift-is-universal.md)

## Proof depends on

- [Polynomials of degree below k form a k-wise independent family](polynomial-k-wise-independent-hashing.md)
- [Multiply-shift is 2/2^M-universal](../word-ram-hash-families/multiply-shift-is-universal.md)

## Sources

- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science, 2012.
- M. N. Wegman and J. L. Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences, 1981.
- M. Dietzfelbinger, T. Hagerup, J. Katajainen and M. Penttonen, "A Reliable Randomized Algorithm for the Closest-Pair Problem", Journal of Algorithms, 1997.
