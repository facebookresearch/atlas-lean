/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.RamanujanExponent

@[expose] public section

open scoped MatrixGroups NumberField

namespace RamanujanExponentTest

open MathlibExt.NumberTheory.RamanujanExponent
open MathlibExt.NumberTheory.SelbergSpectralGap

/-- Every explicit local-exponent family has exponent in `[0, 1/2]`. -/
example {ι : Type*} (F : LocalExponentFamily ι) :
    0 ≤ ramanujanExponentOf F ∧ ramanujanExponentOf F ≤ 1 / 2 :=
  ⟨zero_le_ramanujanExponentOf F, ramanujanExponentOf_le_half F⟩

/-- Every indexed local exponent is at most the family exponent. -/
example {ι : Type*} (F : LocalExponentFamily ι) (i : ι) :
    F.exponent i ≤ ramanujanExponentOf F :=
  exponent_le_ramanujanExponentOf F i

/-- The endpoint `1/2` is admissible for every family in the
Jacquet--Shalika range. -/
example {ι : Type*} (F : LocalExponentFamily ι) :
    IsAdmissible F (1 / 2) :=
  F.exponent_le_half

/-- For `δ = 1/2`, admissibility is detected by the family exponent. -/
example {ι : Type*} (F : LocalExponentFamily ι) :
    IsAdmissible F (1 / 2) ↔ ramanujanExponentOf F ≤ 1 / 2 :=
  isAdmissible_iff_ramanujanExponentOf_le F (by norm_num)

/-- Vanishing of the family exponent is the tempered conclusion. -/
example {ι : Type*} (F : LocalExponentFamily ι) :
    ramanujanExponentOf F = 0 ↔ GeneralizedRamanujanFor F :=
  ramanujanExponentOf_eq_zero_iff F

/-- The supremum and admissible-infimum formulations agree. -/
example {ι : Type*} (F : LocalExponentFamily ι) :
    ramanujanExponentOf F = sInf (admissibleExponents F) :=
  ramanujanExponentOf_eq_sInf_admissibleExponents F

/-- A Satake pair with local exponent at most `δ` forces the displayed
Hecke eigenvalue bound `2N^δ`. -/
example {N t δ : ℝ} {α β : ℂ} (hN : 1 ≤ N) (ht0 : 0 ≤ t)
    (ht : t ≤ δ) (h : IsSatakePair N t α β) :
    ‖α + β‖ ≤ 2 * N ^ δ :=
  hecke_norm_le_two_mul_rpow_of_isSatakePair hN ht0 ht h

/-- At an actual finite place, the same bound uses `N(v)`. -/
example {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) {t δ : ℝ}
    {α β : ℂ} (ht0 : 0 ≤ t) (ht : t ≤ δ)
    (h : IsSatakePair v.residueNorm t α β) :
    ‖α + β‖ ≤ 2 * v.residueNorm ^ δ :=
  hecke_norm_le_two_mul_residueNorm_rpow_of_isSatakePair v ht0 ht h

/-- The canonical Selberg family dominates itself by construction. -/
example : DominatesSelberg selbergFamily :=
  dominatesSelberg_selbergFamily

/-- Any Selberg-dominating family has exponent at least `C₆₁`. -/
example {ι : Type*} (F : LocalExponentFamily ι)
    (hdom : DominatesSelberg F) :
    selbergConstant ≤ ramanujanExponentOf F :=
  selbergConstant_le_of_dominatesSelberg F hdom

/-- An exceptional eigenvalue `3/16` would force the square-root gap
into every Selberg-dominating family's exponent. -/
example {ι : Type*} (F : LocalExponentFamily ι)
    (hdom : DominatesSelberg F) {Γ : Subgroup SL(2, ℤ)}
    (hΓ : IsCongruenceSubgroup Γ) (hlam : IsEigenvalue Γ (3 / 16)) :
    Real.sqrt (1 / 4 - 3 / 16) ≤ ramanujanExponentOf F :=
  sqrt_le_ramanujanExponentOf_of_dominatesSelberg
    F hdom hΓ hlam (by norm_num) (by norm_num)

/-- The currently anchored Selberg slice has exponent exactly `C₆₁`. -/
example : ramanujanExponentOf selbergFamily = selbergConstant :=
  ramanujanExponentOf_selbergFamily

end RamanujanExponentTest
