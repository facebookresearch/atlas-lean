# Floating-point rounding

## Rounding to an integer

- [Nearest-integer rounding with ties to even](rne.md)
- [Rounding error bounded by the distances to neighbouring integers](abs-rne-sub-le-min.md)
- [Round to nearest integer](abs-rne-sub-le.md)
- [Rounding to the nearest integer is within one half](abs-rne-sub-le-half.md)
- [Ties to even for the nearest integer](even-rne-of-abs-sub-eq-half.md)
- [Rounding to nearest preserves integer upper bounds](rne-le-of-le.md)
- [Rounding to nearest preserves integer lower bounds](le-rne-of-le.md)

## Floating-point numbers and rounding

- [Binary floating-point numbers](is-float.md)
- [Floating-point numbers of a bounded format](is-float-in.md)
- [Exponent of the last place](ulp-exp.md)
- [Round to nearest, ties to even](fl.md)
- [Bounds on the scaled significand](scaled-bounds.md)
- [The rounding error at the scale of the last place](fl-sub-eq.md)
- [The relative error bound](abs-fl-sub-le.md)
- [Round to nearest for floating-point numbers](abs-fl-sub-le-of-is-float.md)
- [Floating-point numbers round to themselves](fl-eq-self.md)
- [Ties to even for floating-point rounding](even-of-abs-fl-sub-eq.md)
- [Bound on the rounded significand](abs-rne-le.md)
- [Rounding gives a floating-point number](is-float-fl.md)

## The normal range of a bounded format

- [In the normal range, rounding stays in the format](is-float-in-fl.md)
- [Round to nearest in a bounded format](abs-fl-sub-le-of-is-float-in.md)

## Sterbenz's lemma

- [The difference of floating-point numbers within a factor of two](exists-sub-eq-of-le.md)
- [Sterbenz's lemma](is-float-sub.md)
- [Sterbenz's lemma in a bounded format](is-float-in-sub.md)
- [Floating-point subtraction is exact under Sterbenz's condition](fl-sub-eq-sub.md)

## Error-free transformations

- [Error-free transformation of a product via fused multiply-add](error-free-transformation-of-a-product-via-fused-multiply-ad.md)
- [Error-free transformation of a sum (TwoSum, FastTwoSum)](error-free-transformation-of-a-sum.md)
- [Veltkamp splitting of a floating-point number](veltkamp-splitting.md)
- [Dekker's error-free product without a fused multiply-add](dekker-two-product.md)
- [Floating-point expansions](floating-point-expansions/README.md)

## IEEE arithmetic, double rounding and compilation

- [Total IEEE-style operation semantics with special values and exceptions](total-ieee-style-operation-semantics-with-special-values-and.md)
- [Double rounding through an extended precision](double-rounding-through-an-extended-precision.md)
- [Semantics preservation of floating-point compilation](semantics-preservation-of-floating-point-compilation.md)
- [IEEE operations agree with rounding in the normal range](ieee-operations-agree-with-rounding-in-the-normal-range.md)

## Veltkamp splitting in binary floating-point arithmetic

- [Veltkamp splitting algorithm](veltkamp-split.md)
- [Nonoverlapping](nonoverlapping.md)

## Related topics

- [Rounding error analysis](../rounding-error-analysis/README.md): error bounds for dot products, matrix products and LU factorization built on the relative error bound of $\mathrm{fl}$.
