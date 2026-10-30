/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.CongruenceSubgroupReduction

open scoped MatrixGroups

/-- Reduction modulo `2` maps `Γ(1)` onto `SL(2, ZMod 2)`. -/
example : ∀ g : SL(2, ZMod 2), ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma 1 ∧
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2)) γ = g :=
  CongruenceSubgroup.exists_mem_Gamma_map_eq_of_not_dvd 1 2 (by decide)

/-- `-1` lies in `Γ₁(2)`. -/
example : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma1 2 :=
  (CongruenceSubgroup.neg_one_mem_Gamma1_iff 2).mpr le_rfl

/-- `-1` does not lie in `Γ₁(3)`. -/
example : (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 3 := by
  rw [CongruenceSubgroup.neg_one_mem_Gamma1_iff]
  norm_num
