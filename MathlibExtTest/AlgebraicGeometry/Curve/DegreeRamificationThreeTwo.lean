/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_AlgebraicCurve_six_mul_degree_eq_mul_finrank_of_forall_eq_weightFloor_of_ord_eq_three_two.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.DegreeRamificationThreeTwo

/-! # Tests for degrees of divisors over `K(y)` with ramification orders three and two -/

@[expose] public section

namespace AlgebraicCurve

-- `exactSource` consumer with the original binders.
example (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (y : F) (hy : Transcendental k y)
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin k ({y} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin k ({y} : Set F)) F)
    (h0 : ∀ w : AlgebraicCurve.Place k F, 0 < w.ord y → w.ord y = 3)
    (h1728 : ∀ w : AlgebraicCurve.Place k F, 0 < w.ord (y - 1728) → w.ord (y - 1728) = 2)
    (m : ℕ) (D : AlgebraicCurve.Divisor k F)
    (hD : ∀ w : AlgebraicCurve.Place k F,
      D w = (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
          + (if 0 < w.ord (y - 1728) then ((m : ℤ) * w.ord (y - 1728)) / 2 else 0)
          + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0)) :
    6 * D.degree =
      (m : ℤ) * (Module.finrank ↥(IntermediateField.adjoin k ({y} : Set F)) F : ℤ) :=
  six_mul_degree_eq_mul_finrank_of_forall_eq_weightFloor_of_ord_eq_three_two k y hy hfin hsep
    h0 h1728 m D hD

-- The pole divisor of `x` has degree `[F : K(x)]`, with no assumption on the base field.
example {K F : Type*} [Field K] [Field F] [Algebra K F] {x : F} (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] (D : Divisor K F)
    (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    Divisor.degree D = (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) :=
  Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord_of_isSeparable hx D hD

-- Universe check: the base field and the function field may live in different universes.
universe u v in
example (k : Type u) [Field k] [IsAlgClosed k] {F : Type v} [Field F] [Algebra k F]
    (y : F) (hy : Transcendental k y)
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin k ({y} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin k ({y} : Set F)) F)
    (h0 : ∀ w : Place k F, 0 < w.ord y → w.ord y = 3)
    (h1728 : ∀ w : Place k F, 0 < w.ord (y - 1728) → w.ord (y - 1728) = 2)
    (m : ℕ) (D : Divisor k F)
    (hD : ∀ w : Place k F,
      D w = (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
          + (if 0 < w.ord (y - 1728) then ((m : ℤ) * w.ord (y - 1728)) / 2 else 0)
          + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0)) :
    6 * D.degree =
      (m : ℤ) * (Module.finrank ↥(IntermediateField.adjoin k ({y} : Set F)) F : ℤ) :=
  six_mul_degree_eq_mul_finrank_of_forall_eq_weightFloor_of_ord_eq_three_two k y hy hfin hsep
    h0 h1728 m D hD

end AlgebraicCurve
