/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQStabilizer

/-! Exact cardinality of the actual tensor-fixing subgroup, with every central bit determined. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The 32 phase-corrected candidates are distinct genuine Q elements. -/
theorem generatedFifth_Q_candidates_injective :
    Function.Injective (fun p : ZMod 2 × Fin 16 => generatedFifthQCandidate p.1 p.2) := by
  rintro ⟨b, k⟩ ⟨c, l⟩ h
  have hu := congrArg spinTranslation h
  have hm := congrArg spinModulation h
  simp only [generatedFifthQCandidate, generatedAxisFourthQFromSpin_translation] at hu
  simp only [generatedFifthQCandidate, generatedAxisFourthQFromSpin_modulation] at hm
  have hbc : b = c := by
    have he := congrFun hu 11
    simpa only [Pi.smul_apply, Pi.single_apply, ite_true, smul_eq_mul, mul_one] using he
  have hkl := generatedFifth_modulation_labels_injective
    (golayLabelCoefficients_injective hm)
  exact Prod.ext hbc hkl

/-- The literal 32 candidate coordinates biject with the actual tensor-fixing subgroup. -/
noncomputable def generatedFifthTensorQEquiv :
    (ZMod 2 × Fin 16) ≃ generatedFifthTensorQStabilizer :=
  Equiv.ofBijective (fun p => ⟨generatedFifthQCandidate p.1 p.2,
    generatedFifth_candidate_tensor_fixed p.1 p.2⟩) (by
      constructor
      · intro p r h
        exact generatedFifth_Q_candidates_injective (congrArg Subtype.val h)
      · intro q
        obtain ⟨b, k, hk⟩ := (generatedFifth_tensor_Q_mem_iff q.val).mp q.property
        exact ⟨(b, k), Subtype.ext hk⟩)

/-- The actual common stabilizer of all original fifth tensor columns has order 32. -/
theorem generatedFifth_tensor_Q_card : Nat.card generatedFifthTensorQStabilizer = 32 := by
  rw [← Nat.card_congr generatedFifthTensorQEquiv, Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
