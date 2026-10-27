---
article_id: af_b8d4eb209e881e9ec83890e5
declaration: def
origin: cited
statement: formalized
lean: MvPolynomial.RegularFunction.Jacobian
---

# Jacobian

The Jacobian of a vector valued polynomial function, viewed as a polynomial.

The matrix is indexed as codomain by domain, following Mathlib's matrix
convention: entry `(j, i)` is the partial derivative of the `j`-th component
with respect to the `i`-th variable, so the Jacobian supports `Matrix.mulVec`
and the standard chain-rule multiplication order.

## Depends on

- [Regular Function](regular-function.md)

## Sources

- [MathlibExt, MathlibExt.Algebra.MvPolynomial.RegularFunction](../../../../../sources/v2/MathlibExt.md)
