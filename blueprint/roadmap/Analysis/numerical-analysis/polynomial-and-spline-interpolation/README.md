# Polynomial and spline interpolation

Error analysis of interpolation: divided differences and Newton's form of the interpolating polynomial, the error formula $f(x) - Q_n(x) = f^{(n+1)}(\xi) \prod_j (x - x_j)/(n+1)!$ and its form at the Chebyshev points, Hermite interpolation, and natural cubic splines with their minimal curvature.

## Divided differences

- [Divided differences](divided-differences.md)
- [Explicit formula for divided differences](explicit-formula-for-divided-differences.md)
- [Coefficient of index m − 1 of a polynomial of degree below m from its values at m distinct nodes](coefficient-of-a-polynomial-from-its-values.md): the Mathlib identity behind the explicit formula
- [Newton form of the interpolating polynomial](newton-form-of-the-interpolating-polynomial.md)
- [Recursion for divided differences](recursion-for-divided-differences.md)
- [Divided differences and derivatives](divided-differences-and-derivatives.md)

## Interpolation error

- [Error of polynomial interpolation](interpolation-error-formula.md)
- [Interpolation error at the Chebyshev points](interpolation-error-at-chebyshev-points.md)
- [Error of Hermite interpolation](hermite-interpolation-error.md)

## Barycentric interpolation

- [Barycentric interpolation](barycentric-interpolation/README.md)

## Cubic splines

- [Natural cubic spline](natural-cubic-spline.md)
- [Existence and uniqueness of the natural cubic spline](existence-and-uniqueness-of-the-natural-cubic-spline.md)
- [The natural cubic spline minimizes curvature](minimal-curvature-of-the-natural-cubic-spline.md)

## Related topics

- [Lagrange interpolation](../../approximation-theory/lagrange-interpolation/README.md): the Lagrange form of the interpolating polynomial and the Lebesgue function.
- [Chebyshev series and interpolation](../../approximation-theory/chebyshev-series-and-interpolation/README.md): convergence of Chebyshev interpolants.
- [Numerical quadrature](../numerical-quadrature/README.md): quadrature rules obtained by integrating interpolants.
