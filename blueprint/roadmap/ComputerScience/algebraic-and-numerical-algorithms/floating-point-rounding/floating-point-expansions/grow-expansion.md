# Grow-Expansion adds a float to a nonoverlapping expansion

Let $p \ge 3$, let $e = \sum_{i=1}^m e_i$ be a [nonoverlapping expansion](nonoverlapping-expansion.md) of $p$-bit components sorted in order of increasing magnitude (any $e_i$ may be zero), and let $b$ be a $p$-bit floating-point number, with rounding to nearest and unbounded exponent. Set $Q_0 = b$ and, for $i = 1, \dots, m$, $(Q_i, h_i) = \mathrm{TwoSum}(Q_{i-1}, e_i)$, and $h_{m+1} = Q_m$. Then $h = \sum_{i=1}^{m+1} h_i$ is a nonoverlapping expansion with

$$h = e + b,$$

whose components are in order of increasing magnitude (except that any $h_i$ may be zero). If $e$ is nonadjacent and ties are broken to even, $h$ is nonadjacent.

## Depends on

- [Nonoverlapping floating-point expansion](nonoverlapping-expansion.md)
- [Error-free transformation of a sum (TwoSum, FastTwoSum)](../error-free-transformation-of-a-sum.md)

## Proof depends on

- [The roundoff error of a floating-point sum is small and representable](roundoff-error-of-a-sum-is-small-and-representable.md)
- [Error-free transformation of a sum](../error-free-transformation-of-a-sum.md)

## Sources

- J. R. Shewchuk, "Adaptive precision floating-point arithmetic and fast robust geometric predicates", *Discrete & Computational Geometry* 18(3):305–363, 1997; technical report version CMU-CS-96-140R, Section 2.4, Theorem 10 (algorithm GROW-EXPANSION) and its proof. <https://people.eecs.berkeley.edu/~jrs/papers/robustr.pdf>
