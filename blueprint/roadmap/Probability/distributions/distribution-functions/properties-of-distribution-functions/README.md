# Properties of distribution functions

The distribution function $F(x) = P(X \le x)$ of a real random variable is nondecreasing and
right-continuous, with $F(x) \to 0$ as $x \to -\infty$ and $F(x) \to 1$ as $x \to \infty$.

## Idea

These three properties characterize distribution functions: every function that has them is the
distribution function of some random variable, as the quantile construction shows. Right-continuity comes from the
non-strict inequality in $P(X \le x)$. The left limit is $F(x-) = P(X < x)$, so the jump $F(x) - F(x-) = P(X = x)$ is
the mass of the atom at $x$.

## Statements

- [Properties of the distribution function of a random variable](distribution-function-properties.md)

## Background

- [Atoms of a distribution function](../cumulative-distribution-function/README.md): atoms of a distribution as the jumps of its distribution function
- [Inverse transform sampling](../quantile-function-and-inverse-transform-sampling/inverse-transform-sampling/README.md): the quantile construction, which gives the converse
- [Probability measures on the real line from distribution functions](../../../foundations/probability-measures-from-distribution-functions/README.md): the probability measure with a given distribution function
