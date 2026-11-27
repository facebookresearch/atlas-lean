# Barycentric interpolation

The Lagrange form of the interpolating polynomial can be rewritten so that evaluation costs $O(n)$ operations after $O(n^2)$ to compute weights that do not depend on the data. The second, or true, barycentric formula expresses the interpolant as a ratio of two such sums. For Chebyshev points the weights are explicit and of comparable size, which makes this the standard way to evaluate polynomial interpolants of high degree. The spread of the weights also bounds the Lebesgue constant from below, which shows that equispaced interpolation is exponentially ill-conditioned.

- [Barycentric weights](barycentric-weights.md)
- [First barycentric formula](first-barycentric-formula.md)
- [Second barycentric formula](second-barycentric-formula.md)
- [Barycentric weights for equispaced points](barycentric-weights-for-equispaced-points.md)
- [Barycentric weights for Chebyshev points](barycentric-weights-for-chebyshev-points.md)
- [The Lebesgue constant is bounded below by the ratio of the barycentric weights](lebesgue-constant-bounded-below-by-the-weight-ratio.md)
- [Lebesgue constants of equispaced points grow exponentially](lebesgue-constants-of-equispaced-points-grow-exponentially.md)

## Related topics

- [Lagrange interpolation](../../../approximation-theory/lagrange-interpolation/eval-interpolant.md)
- [Newton form of the interpolating polynomial](../newton-form-of-the-interpolating-polynomial.md)
