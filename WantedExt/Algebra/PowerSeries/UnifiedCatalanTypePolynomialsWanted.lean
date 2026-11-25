/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Exp
public import MathlibExt.Algebra.PowerSeries.CatalanTypeKernelDecomposition
public import MathlibExt.Algebra.PowerSeries.CatalanTypeMatrixDeterminant
public import MathlibExt.Algebra.PowerSeries.HermiteShiftConvolution
public import MathlibExt.Algebra.PowerSeries.UnifiedCatalanTypePolynomials

/-!
# Unified Catalan-type polynomials

Statements from M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105.

Every family in the paper is defined by a generating function of the shape
`numerator(t) / (c - α t + β t^m)^λ` with a real exponent `λ`. The denominator factor
`(c - α t + β t^m)^(-λ)` is `trinomialNegPowSeries λ c α β m`, built from Mathlib's binomial
series; the paper's polynomials are coefficients of products of power series in `t`, with
all variables `x, y, z` fixed real numbers. The paper's `P^λ_{r,m}(z)` and `h^λ_{r,m}(z)`
in Theorems 2 and 3 are read as the coefficients of `(1 - m t + z t^m)^(-λ)` and
`(1 - m z t + t^m)^(-λ)` (Definition 5 with `A = 0`), as in the proof of Theorem 2.
The paper's Hermite polynomials `H_n(x)` have the generating function `e^(2xt - t²)`
(Section 1), and `H_n(x, y)` are the Kampé de Fériet polynomials `H^2_n(x, y)` of
Equation (2).

Proved in `MathlibExt.Algebra.PowerSeries.UnifiedCatalanTypePolynomials`, which this module
imports: `coeff_nietoHermiteSeries_mul_trinomialNegPowSeries` and `det_catalanTypeHankel_eq_zero`.

The lower-triangular determinant formula is proved in and re-exported from
`MathlibExt.Algebra.PowerSeries.CatalanTypeMatrixDeterminant`.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

end

end MetaMathlibExt
