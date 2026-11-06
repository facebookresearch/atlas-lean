/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSignParameters

/-! The ten-parameter sign space is bound to the actual original seventh matrix constraints. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The finite syndrome rows are the original physical Golay coordinate differences. -/
theorem generatedSeventhSignParameter_entry (i : Fin 2) (j : Fin 12) :
    generatedSeventhSignParameterMatrix i j =
      (golayGeneratorBit j 16 : ZMod 2) +
        (golayGeneratorBit j ((![17, 19] : Fin 2 → Fin 24) i) : ZMod 2) := by
  revert i j
  decide +kernel

/-- The actual finite syndrome applies by the original physical triangle-sign differences. -/
theorem generatedSeventhSignParameter_apply (v : Fin 12 → ZMod 2) (i : Fin 2) :
    (generatedSeventhSignParameterMatrix *ᵥ v) i =
      golayEncoder v 16 + golayEncoder v ((![17, 19] : Fin 2 → Fin 24) i) := by
  change (∑ j, generatedSeventhSignParameterMatrix i j * v j) = _
  simp_rw [generatedSeventhSignParameter_entry, add_mul]
  rw [Finset.sum_add_distrib]
  simp only [golayEncoder, mul_comm]
  rfl

/-- The syndrome kernel is equality of the three actual physical triangle signs. -/
theorem generatedSeventhSignParameter_mem_iff (v : Fin 12 → ZMod 2) :
    v ∈ generatedSeventhSignParameterSpace ↔
      golayEncoder v 16 = golayEncoder v 17 ∧ golayEncoder v 16 = golayEncoder v 19 := by
  have hbin : ∀ u w : ZMod 2, u + w = 0 ↔ u = w := by decide
  change generatedSeventhSignParameterMatrix *ᵥ v = 0 ↔ _
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    rw [generatedSeventhSignParameter_apply] at h0 h1
    exact ⟨(hbin _ _).mp h0, (hbin _ _).mp h1⟩
  · rintro ⟨h0, h1⟩
    ext i
    rw [generatedSeventhSignParameter_apply]
    fin_cases i
    · exact (hbin _ _).mpr h0
    · exact (hbin _ _).mpr h1

/-- Literal original code labels whose genuine sign isometry fixes the entire seventh matrix. -/
def generatedSeventhSpatialSignLabels : Set (Fin 4096) :=
  {a | golaySignIsometry (sourceGeneratedSignCode a) ∈ generatedSeventhSpatialStabilizer}

/-- The literal matrix-preserving sign labels are equivalent to the genuine ten-parameter kernel. -/
def generatedSeventhSpatialSignLabelsEquiv :
    generatedSeventhSpatialSignLabels ≃ generatedSeventhSignParameterSpace where
  toFun a := ⟨golayLabelCoefficients a.val,
    (generatedSeventhSignParameter_mem_iff _).mpr
      ((generatedSeventh_sign_spatial_mem_iff a.val).mp a.property)⟩
  invFun v := ⟨sourceCodeLabelEquiv.symm v.val, by
    apply (generatedSeventh_sign_spatial_mem_iff _).mpr
    rw [show golayLabelCoefficients (sourceCodeLabelEquiv.symm v.val) = v.val from
      sourceCodeLabelEquiv.apply_symm_apply v.val]
    exact (generatedSeventhSignParameter_mem_iff v.val).mp v.property⟩
  left_inv a := by
    apply Subtype.ext
    exact sourceCodeLabelEquiv.symm_apply_apply a.val
  right_inv v := by
    apply Subtype.ext
    exact sourceCodeLabelEquiv.apply_symm_apply v.val

/-- Exactly 1024 literal original Golay sign labels fix the actual seventh matrix. -/
theorem generatedSeventhSpatialSignLabels_card :
    Nat.card generatedSeventhSpatialSignLabels = 1024 := by
  rw [Nat.card_congr generatedSeventhSpatialSignLabelsEquiv,
    generatedSeventhSignParameterSpace_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
