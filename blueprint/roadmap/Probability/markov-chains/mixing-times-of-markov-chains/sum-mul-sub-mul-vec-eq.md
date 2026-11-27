# The Dirichlet form of a reversible matrix

Let $S$ be a finite set, $\pi : S \to \mathbb{R}$, and $P$ a real $S \times S$ matrix with unit
row sums, $\sum_y P(x, y) = 1$ for every $x$, in detailed balance with $\pi$:
$\pi(x) P(x, y) = \pi(y) P(y, x)$ for all $x, y$. Then for every $g : S \to \mathbb{R}$,

$$\sum_{x} \pi(x)\, g(x) \bigl(g(x) - (Pg)(x)\bigr) = \frac{1}{2} \sum_{x, y} \bigl(g(x) - g(y)\bigr)^2 \pi(x) P(x, y),$$

where $(Pg)(x) = \sum_y P(x, y)\, g(y)$. This is the identity behind the variational
characterisation (5) of the spectral gap in Sinclair's paper.

## Background

- [Dirichlet form of a sub-Markovian generator on a finite set](../dirichlet-forms/form.md): the general
  form (Fukushima, Oshima and Takeda, Example 1.2.5), of which the right side is the kernel case $Q = P - 1$;
  [Sinclair's identity in Dirichlet-form terms](../dirichlet-forms/form-sub-one-self-eq-sum-mul-sub-mul-vec.md)
  restates this identity there.

## Sources

- A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*,
  Combinatorics, Probability and Computing 1 (1992), 351–370, equation (5).
