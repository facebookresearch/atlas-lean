# Tilted large deviation principle

Let probability measures $(\mu_n)$ on a topological space $X$ satisfy the large deviation
principle with rate function $I$ (not necessarily good), and let $F : X \to \mathbb{R}$ be
continuous and bounded. Then the tilted measures

$$Q_n(A) = \frac{\int_A e^{n F} \, d\mu_n}{\int_X e^{n F} \, d\mu_n}$$

satisfy the large deviation principle with rate function

$$J(x) = S - \bigl(F(x) - I(x)\bigr), \qquad S = \sup_{y \in X} \bigl(F(y) - I(y)\bigr),$$

where $S$ is finite. $J$ vanishes exactly at the maximisers of $F - I$, so when that maximiser is
unique the tilted measures concentrate there.

The denominator is handled by Varadhan's integral lemma, and the numerator by its two bounds
restricted to an open set (lower bound) and to a closed set (upper bound).

## Informally uses

- [Varadhan's integral lemma](../varadhan-s-integral-lemma/tendsto-log-lintegral-exp.md): Varadhan's
  proof of Theorem 2.11 repeats the proof of the integral lemma (Theorem 2.8) on a closed set and
  on the whole space, and takes the difference of the logarithms.

## Sources

- S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010, Section 2, Theorem 2.11 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf).
