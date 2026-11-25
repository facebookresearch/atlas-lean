/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomialData

@[expose] public section

open ModularCurve

/-- Source-shaped consumer: the level-one exemplar inhabits the carrier. -/
example : Nonempty (ModularPolynomialData 1) :=
  ModularCurve.nonempty_modularPolynomialData_one

/-- The exemplar polynomial is `X - Y`, monic of degree one in the outer
variable. -/
example : modularPolynomialDataOne.Φ = Polynomial.X - Polynomial.C Polynomial.X :=
  rfl

example : modularPolynomialDataOne.Φ.Monic := modularPolynomialDataOne.monic

example : modularPolynomialDataOne.Φ.natDegree = ArithmeticFunction.dedekindPsi 1 :=
  modularPolynomialDataOne.natDegree_eq

/-- Boundary check: the degree function records level one correctly. -/
example : ArithmeticFunction.dedekindPsi 1 = 1 := ArithmeticFunction.dedekindPsi_one

/-- `qExpand` substitutes `q ↦ q ^ N` at a negative exponent: for `N = 3`,
`5 q⁻²` goes to `5 q⁻⁶`. -/
example : qExpand ℚ 3 (HahnSeries.single (-2 : ℤ) (5 : ℚ)) = HahnSeries.single (-6 : ℤ) 5 := by
  rw [qExpand_single]
  norm_num

/-- Off the image of `k ↦ N k` the coefficient is zero: `j(q²)` has no `q⁻¹` term. -/
example : (jqN 2).coeff (-1 : ℤ) = 0 :=
  qExpand_coeff_of_not_dvd 2 jq (by decide)

/-- On the image the coefficient is carried over: the `q⁻²` coefficient of `j(q²)`
is the `q⁻¹` coefficient of `j(q)`, which is `1`. -/
example : (jqN 2).coeff (-2 : ℤ) = 1 := by
  rw [jqN, show (-2 : ℤ) = ((2 : ℕ) : ℤ) * (-1) by norm_num, qExpand_coeff_mul, coeff_jq_neg_one]

/-- Composing substitutions multiplies the exponents: `q ↦ q³` followed by
`q ↦ q²` is `q ↦ q⁶`. -/
example (f : LaurentSeries ℚ) : qExpand ℚ 2 (qExpand ℚ 3 f) = qExpand ℚ 6 f :=
  qExpand_qExpand 3 2 f

example : qExpand ℚ 2 (qExpand ℚ 3 (HahnSeries.single (-1 : ℤ) (1 : ℚ))) =
    HahnSeries.single (-6 : ℤ) 1 := by
  rw [qExpand_qExpand, qExpand_single]
  norm_num

/-- The vanishing field of the carrier, at the exemplar. -/
example : modularPolynomialDataOne.Φ.eval₂ evalAtJ (jqN 1) = 0 :=
  modularPolynomialDataOne.eval_eq_zero

/-- The same vanishing, computed: `X - Y` is zero at `(j(q), j(q))`. -/
example : (Polynomial.X - Polynomial.C Polynomial.X : Polynomial (Polynomial ℤ)).eval₂ evalAtJ
    (jqN 1) = 0 := by
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, evalAtJ_X, jqN_one, sub_self]

/-- The vanishing condition depends on the level: `X - Y` is not zero at
`(j(q), j(q²))`, since the `q⁻¹` coefficient of `j(q²) - j(q)` is `-1`. -/
example : (Polynomial.X - Polynomial.C Polynomial.X : Polynomial (Polynomial ℤ)).eval₂ evalAtJ
    (jqN 2) ≠ 0 := by
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, evalAtJ_X]
  intro h
  have h1 := congrArg (fun f : LaurentSeries ℚ => f.coeff (-1 : ℤ)) h
  simp only [HahnSeries.coeff_sub, HahnSeries.coeff_zero, coeff_jq_neg_one, jqN,
    qExpand_coeff_of_not_dvd 2 jq (by decide : ¬ ((2 : ℕ) : ℤ) ∣ -1)] at h1
  norm_num at h1
