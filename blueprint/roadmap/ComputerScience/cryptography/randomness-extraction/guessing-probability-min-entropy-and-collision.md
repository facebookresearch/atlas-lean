# Guessing probability, min-entropy and collision probability

Let $X$ have probability mass function $p$ on a nonempty finite set $S$. A fixed guess $x$ succeeds with probability $p(x)$, so the best such guess succeeds with probability $\gamma(X)=\max_{x\in S}p(x)$. The **min-entropy** of $X$, in bits, is

$$
H_\infty(X)=-\log_2\gamma(X).
$$

The maximum is positive because the masses sum to one; individual outcomes may have mass zero. The [point-mass criterion](le-min-entropy-iff.md) says that, for every real $k$, $H_\infty(X)\ge k$ exactly when $p(x)\le 2^{-k}$ for every $x\in S$.

Instead of making a fixed guess, draw $X'$ independently from the same law. The [collision probability](collision-probability.md) is $\Pr[X=X']$. Independence gives $p(x)^2$ for the event that both draws equal $x$; summing over these disjoint events gives the [sum-of-squares formula](collision-probability-eq-sum-sq.md). In particular, the collision probability is [at most the largest point mass](../../../InformationTheory/not-yet-classified/part-01/leftover-hash/collision-le-of-le.md).

## Sources

- D. Boneh and V. Shoup, [*A Graduate Course in Applied Cryptography*, v0.4](https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_4.pdf), 2017, §8.10.4, p. 329 (guessing probability, immediately before Theorem 8.11).
- S. Vadhan, [*Pseudorandomness*](https://people.seas.harvard.edu/~salil/pseudorandomness/pseudorandomness-published-Dec12.pdf), 2012, Definition 4.7, p. 85 (collision probability); Definitions 6.7 and 6.9, pp. 171 and 173 (base-two min-entropy and the point-mass criterion).
