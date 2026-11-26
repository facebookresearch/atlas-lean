# The birthday distinguisher against a block cipher viewed as a PRF

Let $E$ be any block cipher on a block set of size $N$, and let the distinguisher query $Q \le N$ distinct blocks and output $1$ iff two answers coincide. Against $E$ it never outputs $1$; against a random function its advantage is exactly $1 - \frac{N(N-1)\cdots(N-Q+1)}{N^Q}$, which is at least

$$\min\Bigl(\frac{Q(Q-1)}{4N},\ 0.63\Bigr),$$

and at least $1/2$ when $Q = N \ge 2$ (Boneh and Shoup, Section 4.4.3 and Theorem B.1). Consequently a block cipher whose block space $N = 2^{b(n)}$ is not super-polynomial (and $b(n) \ge 1$ eventually) is not a PRF: with $q = \min(Q(n), N)$ polynomially many queries the advantage is non-negligible.

## Proof sketch

Answers of a permutation on distinct inputs are distinct. The no-collision probability for a random function is the falling-factorial ratio; the lower bound is the standard birthday estimate $1 - e^{-Q(Q-1)/2N}$ together with $1 - e^{-x} \ge \min(x/2, 1 - e^{-1})$.

## Depends on

- [Block cipher (uniform family)](block-cipher.md)
- [PRF advantage](../pseudorandom-functions/prf-advantage.md)

## Proof depends on

- [Birthday lower bound](../../hash-functions/birthday-bound/collision-prob-ge.md)
- [Birthday lower bound, exponential form](../../hash-functions/birthday-bound/one-sub-exp-le-collision-prob.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
