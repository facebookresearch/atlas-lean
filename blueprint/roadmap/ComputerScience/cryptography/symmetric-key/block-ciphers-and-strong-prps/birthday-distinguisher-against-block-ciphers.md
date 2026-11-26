# The birthday distinguisher against a block cipher viewed as a PRF

Let $E$ be any block cipher with block length $b \ge 1$, so its block set has $N = 2^b$ elements, and let the distinguisher query $Q \le N$ distinct blocks and output $1$ iff two answers coincide. Against $E$ it never outputs $1$; against a random function its advantage is exactly $1 - \frac{N(N-1)\cdots(N-Q+1)}{N^Q}$, which is at least

$$1 - e^{-Q(Q-1)/2N},$$

and at least $0.316 \cdot Q(Q-1)/N \ge Q(Q-1)/(4N)$ when $1 \le Q \le \sqrt{2N}$ (Bellare, Kilian and Rogaway, Proposition 2.4 and Proposition A.1). Consequently a block cipher whose block space $N = 2^{b(n)}$ is not super-polynomial (and $b(n) \ge 1$ eventually) is not a PRF: if $N \le p(n)$ for a polynomial $p$ and infinitely many $n$, then $Q = \min(\lfloor\sqrt{2N}\rfloor, p(n))$ queries give advantage at least $0.316 \cdot Q(Q-1)/N \ge 0.158$ on those $n$, which is non-negligible.

## Proof sketch

Answers of a permutation on distinct inputs are distinct. The no-collision probability for a random function is the falling-factorial ratio; the lower bounds are the standard birthday estimates $1 - e^{-Q(Q-1)/2N}$ and, for $Q \le \sqrt{2N}$, $0.316 \cdot Q(Q-1)/N$. With $Q = \lfloor\sqrt{2N}\rfloor$ and $N \ge 2$ one has $Q(Q-1)/N \ge 1/2$.

## Depends on

- [Block cipher (uniform family)](block-cipher.md)
- [PRF advantage](../pseudorandom-functions/prf-advantage.md)

## Proof depends on

- [Birthday lower bound](../../hash-functions/birthday-bound/collision-prob-ge.md)
- [Birthday lower bound, exponential form](../../hash-functions/birthday-bound/one-sub-exp-le-collision-prob.md)

## Sources

- M. Bellare, J. Kilian and P. Rogaway, "The Security of the Cipher Block Chaining Message Authentication Code", Journal of Computer and System Sciences 61(3), 2000, pp. 362–399, Proposition 2.4 (birthday attack on a family of permutations viewed as a PRF) and Proposition A.1 (birthday bounds).
