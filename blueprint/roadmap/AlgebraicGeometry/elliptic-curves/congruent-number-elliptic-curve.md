# A positive integer n is congruent iff the curve y^2 = x^3 − n^2 x has a rational point with y ≠ 0

Let $n$ be a positive integer, and let $E_n$ be the elliptic curve $y^2 = x^3 - n^2 x$ over $\mathbb{Q}$. It is an elliptic curve because $4(-n^2)^3 = -4n^6 \neq 0$. Then $n$ is a congruent number if and only if there is a point $(x, y) \in E_n(\mathbb{Q})$ with $y \neq 0$.

## Proof sketch

Given positive rationals $a, b, c$ with $a^2 + b^2 = c^2$ and $ab = 2n$, set $x = c^2/4$ and $y = c(a^2 - b^2)/8$. Then $x \mp n = (a \mp b)^2/4$, so $x^3 - n^2 x = y^2$. Moreover $y \neq 0$, since $a = b$ would give $c^2 = 2a^2$, contradicting the irrationality of $\sqrt{2}$. Conversely, given a rational point with $y \neq 0$, we have $x \neq 0, \pm n$. Put $a = |x^2 - n^2|/|y|$, $b = |2nx|/|y|$ and $c = (x^2 + n^2)/|y|$. These are positive rationals, and direct computation gives $a^2 + b^2 = c^2$ and $\tfrac12 ab = n$.

## Expansion

A good expansion of this node links each prerequisite of its statement: Elliptic curve in Weierstrass form over a field of characteristic not 2 or 3.

## Depends on

- [Congruent number: a positive integer that is the area of a right triangle with rational sides](congruent-number.md)

## Proof depends on

- [The square root of 2 is irrational](../../NumberTheory/diophantine-approximation/transcendence-irrationality/sqrt-two-irrational.md)

## Sources

- William Stein, Elementary Number Theory: Primes, Congruences, and Secrets. A Computational Approach, Undergraduate Texts in Mathematics, Springer, 2009.
