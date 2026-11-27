# Floating-point expansions

An expansion represents a real number exactly as an unevaluated sum $x_n + \dots + x_1$ of floating-point numbers. If its components are nonoverlapping, its sign is the sign of the largest component and the largest component approximates its value. The roundoff error of a floating-point sum is itself a floating-point number no larger than either summand, so error-free transformations such as Two-Sum can grow an expansion one component at a time while keeping it nonoverlapping; this is the basis of exact geometric predicates.

- [Nonoverlapping floating-point expansion](nonoverlapping-expansion.md)
- [The roundoff error of a floating-point sum is small and representable](roundoff-error-of-a-sum-is-small-and-representable.md)
- [Grow-Expansion adds a float to a nonoverlapping expansion](grow-expansion.md)

## Related topics

- [Error-free transformation of a sum (TwoSum, FastTwoSum)](../error-free-transformation-of-a-sum.md)
- [Veltkamp splitting](../veltkamp-splitting.md)
