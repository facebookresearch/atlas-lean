/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismIncidence

/-! Actual Golay sign spaces vanishing on a specified physical octad. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual Golay words whose signs are positive on every specified support coordinate. -/
def generatedNinthOctadSignSpace (s : Fin 4096) : Submodule (ZMod 2) golayCode where
  carrier := {c | ∀ i : Fin 24, (golayEncodedMask s.val).testBit i.val = true → c.val i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by
    intro c d hc hd i hi
    change c.val i + d.val i = 0
    rw [hc i hi, hd i hi, add_zero]
  smul_mem' := by
    intro a c hc i hi
    change a * c.val i = 0
    rw [hc i hi, mul_zero]

/-- Twelve-bit labels whose original encoded words vanish on the specified octad. -/
def generatedNinthOctadSignLabels (s : Fin 4096) : Finset (Fin 4096) :=
  Finset.univ.filter (fun d => ∀ i : Fin 24,
    (golayEncodedMask s.val).testBit i.val = true →
      (golayEncodedMask d.val).testBit i.val = false)

/-- The original mask condition is precisely membership in the actual sign subspace. -/
theorem generatedNinth_octad_sign_label_mem (s d : Fin 4096) :
    d ∈ generatedNinthOctadSignLabels s ↔ golayCodeLabelEquiv d ∈
      generatedNinthOctadSignSpace s := by
  simp only [generatedNinthOctadSignLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  change (∀ i : Fin 24, _ → _) ↔ (∀ i : Fin 24, _ → _)
  have hz : ∀ i : Fin 24, (golayEncodedMask d.val).testBit i.val = false ↔
      (golayCodeLabelEquiv d).val i = 0 := by
    intro i
    rw [golayCodeLabelEquiv_val, ← ZMod.val_eq_zero, golayLabelEncoder_match]
    cases (golayEncodedMask d.val).testBit i.val <;> simp
  simp only [hz]

/-- The actual code encoder identifies finite labels with every member of the sign space. -/
def generatedNinthOctadSignEquiv (s : Fin 4096) :
    ↥(generatedNinthOctadSignLabels s) ≃ generatedNinthOctadSignSpace s where
  toFun d := ⟨golayCodeLabelEquiv d.val,
    (generatedNinth_octad_sign_label_mem s d.val).mp d.property⟩
  invFun c := ⟨golayCodeLabelEquiv.symm c.val, by
    apply (generatedNinth_octad_sign_label_mem s _).mpr
    rw [golayCodeLabelEquiv.apply_symm_apply]
    exact c.property⟩
  left_inv d := Subtype.ext (golayCodeLabelEquiv.symm_apply_apply d.val)
  right_inv c := Subtype.ext (golayCodeLabelEquiv.apply_symm_apply c.val)

/-- Counting original labels counts the entire actual Golay sign subspace. -/
theorem generatedNinth_octad_sign_space_card (s : Fin 4096) :
    Nat.card (generatedNinthOctadSignSpace s) = (generatedNinthOctadSignLabels s).card := by
  rw [← Nat.card_congr (generatedNinthOctadSignEquiv s), Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
