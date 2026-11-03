/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.Subgroup.SupZpowers
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

@[expose] public section

open scoped MatrixGroups

example {G : Type*} [Group G] (Γ : Subgroup G) {c : G}
    (hc : c ∈ Subgroup.center G) (hc2 : c ^ 2 = 1) (g : G) :
    g ∈ Γ ⊔ Subgroup.zpowers c ↔ g ∈ Γ ∨ c * g ∈ Γ :=
  Subgroup.mem_sup_zpowers_iff_of_central_sq_eq_one Γ hc hc2 g

example (g : Multiplicative (ZMod 2)) :
    g ∈ (⊥ : Subgroup (Multiplicative (ZMod 2))) ⊔
        Subgroup.zpowers (Multiplicative.ofAdd 1) ↔
      g ∈ (⊥ : Subgroup (Multiplicative (ZMod 2))) ∨
        Multiplicative.ofAdd 1 * g ∈ (⊥ : Subgroup (Multiplicative (ZMod 2))) :=
  Subgroup.mem_sup_zpowers_iff_of_central_sq_eq_one ⊥
    (Subgroup.mem_center_iff.mpr fun _ => mul_comm _ _)
    (by decide) g

example (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ g ∈ Γ ∨ -g ∈ Γ := by
  have hcent : (-1 : SL(2, ℤ)) ∈ Subgroup.center (SL(2, ℤ)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.coe_neg]
  have hneg : ∀ x : SL(2, ℤ), (-1 : SL(2, ℤ)) * x = -x := by
    intro x
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.coe_neg]
  have h := Subgroup.mem_sup_zpowers_iff_of_central_sq_eq_one Γ hcent
    (by simp : (-1 : SL(2, ℤ)) ^ 2 = 1) g
  rw [hneg] at h
  exact h
