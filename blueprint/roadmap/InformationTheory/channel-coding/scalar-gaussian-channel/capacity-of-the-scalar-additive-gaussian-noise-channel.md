# Capacity of the scalar additive Gaussian noise channel

Let $N > 0$ and $P \ge 0$, and let $Z$ be a real random variable with law $N(0, N)$. For a real random variable $X$
independent of $Z$, write $I(X; X + Z)$ for the mutual information in bits, a value in $[0, \infty]$. Then

$$\sup\Big\{ I(X; X + Z) : X \text{ independent of } Z,\ \mathbb E X^2 \le P \Big\} = \tfrac12 \log_2\Big(1 + \frac{P}{N}\Big),$$

the supremum running over all laws of $X$ with second moment at most $P$, centered or not, and it is attained by $X$ with law
$N(0, P)$ (the constant $X = 0$ when $P = 0$). This is the information capacity of the channel $Y = X + Z$ under the power
constraint; it is a statement about mutual information, not an operational coding theorem.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: among real random variables with variance at most $s > 0$, the law $N(0, s)$ has the largest differential
  entropy, $\tfrac12 \log_2(2\pi e s)$ bits.
- Proof prerequisite: for $Z$ with law $N(0, N)$ independent of $X$, $I(X; X + Z) = h(X + Z) - h(Z)$ whenever the right side is
  defined, with $h(Z) = \tfrac12 \log_2(2\pi e N)$ bits.

## Sources

- T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd edition, Wiley, 2006, Chapter 9 (the Gaussian channel).
- C. E. Shannon, "A mathematical theory of communication", *Bell System Technical Journal* 27:379–423 and 623–656, 1948.
