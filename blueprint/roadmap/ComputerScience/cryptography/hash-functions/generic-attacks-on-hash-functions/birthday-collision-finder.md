# The birthday collision finder

Let $f : M \to D$ with $M, D$ finite. Sampling $s$ independent uniform messages and searching their digests for a collision with distinct messages makes $s$ evaluations of $f$, never outputs a non-collision, and succeeds with probability at least

$$1 - e^{-s(s-1)/(2|D|)} - \binom{s}{2}\frac{1}{|M|}.$$

When $|M| \ge 100|D|$ and $s = \lceil 2\sqrt{|D|}\,\rceil + 1$, the success probability is at least $1/2$ (Boneh and Shoup, Lemma 8.2). The bound holds for every $f$, not only for regular functions.

## Proof sketch

The probability of a digest collision is minimized when $f$ is regular, where it is at least the birthday bound (Boneh and Shoup, Corollary B.2); subtract the probability that two of the sampled messages are themselves equal.

## Depends on

- [Collision resistance and target collision resistance](../collision-resistance-and-target-collision-resistance.md)
- [The collision experiment](../birthday-bound/collision-game.md)

## Proof depends on

- [Birthday lower bound, exponential form](../birthday-bound/one-sub-exp-le-collision-prob.md)
- [Brute-force collision search](brute-force-collision-search.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
