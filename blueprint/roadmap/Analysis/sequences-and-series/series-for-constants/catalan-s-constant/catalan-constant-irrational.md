# Irrationality of Catalan’s constant

Catalan’s constant

$$
G=\sum_{j=0}^{\infty}\frac{(-1)^j}{(2j+1)^2}
$$

is irrational: no rational number equals this real sum.

## Depends on

- [Catalan’s constant](catalan-constant.md)

## Expansion

Use the convergent alternating series as the target. Decompose the irrationality argument into the determinant factorization, denominator divisibility at the finite places, and the real-place decay and nonvanishing estimates for the resulting forms in $1,G$. Verify that the forms are integral after clearing denominators and tend to zero while remaining nonzero under a rationality assumption.

## Sources

- [Catalan.lean — `catalan_irrational`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Catalan.lean#L7-L10)
