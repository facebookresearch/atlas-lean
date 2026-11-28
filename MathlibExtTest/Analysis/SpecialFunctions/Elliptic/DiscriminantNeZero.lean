/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.DiscriminantNeZero

/-! Tests for `MathlibExt.Analysis.SpecialFunctions.Elliptic.DiscriminantNeZero`. -/

open scoped UpperHalfPlane

#check @PeriodPair.G_ofTau_eq_tsum
#check @PeriodPair.discriminant_ofTau_eq_eta
#check @PeriodPair.discriminant_ne_zero

/-- The square lattice `ℤ + ℤ i` has nonzero discriminant. -/
example : (PeriodPair.ofTau UpperHalfPlane.I UpperHalfPlane.I.im_pos.ne').g₂ ^ 3 -
    27 * (PeriodPair.ofTau UpperHalfPlane.I UpperHalfPlane.I.im_pos.ne').g₃ ^ 2 ≠ 0 :=
  PeriodPair.discriminant_ne_zero _

/-- A scaled period pair has nonzero discriminant. -/
example (L : PeriodPair) (α : ℂˣ) : (L.scale α).g₂ ^ 3 - 27 * (L.scale α).g₃ ^ 2 ≠ 0 :=
  (L.scale α).discriminant_ne_zero

/-- At `τ = i`, `G₄` is the sum of `(m i + n)⁻⁴` over `ℤ²`. -/
example : (PeriodPair.ofTau UpperHalfPlane.I UpperHalfPlane.I.im_pos.ne').G 4 =
    ∑' v : Fin 2 → ℤ, (((v 0 : ℂ) * UpperHalfPlane.I + v 1) ^ 4)⁻¹ :=
  PeriodPair.G_ofTau_eq_tsum _ 4
