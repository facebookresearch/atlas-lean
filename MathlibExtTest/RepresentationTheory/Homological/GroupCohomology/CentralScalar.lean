/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CentralScalar

import Mathlib.Tactic.NormNum.Prime
#check @groupCohomology.isZero_H0_of_smul
#check @groupCohomology.isZero_H1_of_central_smul
#check @Matrix.GeneralLinearGroup.isZero_H0_and_H1_stdRep
#check @Matrix.GeneralLinearGroup.isZero_H0_and_H1_stdRep_zmod

-- `H¹(GL₂(𝔽₅), 𝔽₅²) = 0`.
example : CategoryTheory.Limits.IsZero
    (groupCohomology.H1 (Rep.of (Matrix.GeneralLinearGroup.stdRep (Fin 2) (ZMod 5)))) :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  (Matrix.GeneralLinearGroup.isZero_H0_and_H1_stdRep_zmod 5 (by norm_num)).2

-- Over `ℚ`, `H⁰` and `H¹` of `GL₃(ℚ)` on `ℚ³` vanish.
example : CategoryTheory.Limits.IsZero
      (groupCohomology.H0 (Rep.of (Matrix.GeneralLinearGroup.stdRep (Fin 3) ℚ))) ∧
    CategoryTheory.Limits.IsZero
      (groupCohomology.H1 (Rep.of (Matrix.GeneralLinearGroup.stdRep (Fin 3) ℚ))) :=
  Matrix.GeneralLinearGroup.isZero_H0_and_H1_stdRep (Fin 3) ℚ (by norm_num)

-- The general theorems for a group that is not a matrix group: the group `ℤˣ = {±1}` of order
-- `2` acts on `ℚ` through the sign, so its generator `-1` is central and acts by `-1`, and
-- `-1 - 1 = -2` is a unit of `ℚ`.
example :
    CategoryTheory.Limits.IsZero (groupCohomology.H0 (Rep.of
      ((Units.coeHom (Module.End ℚ ℚ)).comp
        (Units.map (algebraMap ℤ (Module.End ℚ ℚ)).toMonoidHom)))) ∧
    CategoryTheory.Limits.IsZero (groupCohomology.H1 (Rep.of
      ((Units.coeHom (Module.End ℚ ℚ)).comp
        (Units.map (algebraMap ℤ (Module.End ℚ ℚ)).toMonoidHom)))) := by
  have hρ : ∀ v : ℚ, (Rep.of ((Units.coeHom (Module.End ℚ ℚ)).comp
      (Units.map (algebraMap ℤ (Module.End ℚ ℚ)).toMonoidHom))).ρ (-1) v = (-1 : ℚ) • v :=
    fun v => by simp
  have hc : IsUnit ((-1 : ℚ) - 1) := by norm_num
  exact ⟨groupCohomology.isZero_H0_of_smul _ hc hρ,
    groupCohomology.isZero_H1_of_central_smul _
      (Subgroup.mem_center_iff.2 fun g => mul_comm g (-1)) hc hρ⟩

-- The general theorems in an arbitrary universe: a central element acting by `-1` over a
-- ring in which `2` is a unit.
example {k G : Type 1} [CommRing k] [Group G] (A : Rep k G) {z : G}
    (hz : z ∈ Subgroup.center G) (h2 : IsUnit (2 : k)) (hρ : ∀ v, A.ρ z v = (-1 : k) • v) :
    CategoryTheory.Limits.IsZero (groupCohomology.H0 A) ∧
      CategoryTheory.Limits.IsZero (groupCohomology.H1 A) := by
  have hc : IsUnit ((-1 : k) - 1) := by
    rw [show (-1 : k) - 1 = -2 by ring]
    exact h2.neg
  exact ⟨groupCohomology.isZero_H0_of_smul A hc hρ,
    groupCohomology.isZero_H1_of_central_smul A hz hc hρ⟩
