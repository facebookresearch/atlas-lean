/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTraversalData

/-! Complete actual source generation of the whole 720-element permutation flag group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Each original source generator preserves the entire actual standard octad. -/
def generatedTenthAxisLowerRecoveryOctadGenerator (k : Fin 2) :
    generatedTenthE7OctadPermutationGroup :=
  ⟨generatedTenthAxisLowerRecoveryPermutation k,
    (generatedTenth_e7_octad_permutation_mem _).mpr
      (generatedTenth_axis_lower_recovery_source_flags k).1⟩

/-- Both genuine source generators fix the complete actual standard normal pair. -/
theorem generatedTenth_axis_lower_recovery_generator_pair : ∀ k : Fin 2,
    generatedTenthAxisLowerRecoveryOctadGenerator k • generatedTenthE7OctadPairDataElement 22 =
      generatedTenthE7OctadPairDataElement 22 := by
  intro k
  apply Subtype.ext
  have h : ∀ k : Fin 2,
      (generatedTenthE7OctadPairData 22).map
        (generatedTenthE7OctadPointPermutationHom
          (generatedTenthAxisLowerRecoveryOctadGenerator k)).toEmbedding =
        generatedTenthE7OctadPairData 22 := by
    decide +kernel
  exact h k

/-- Both genuine source generators fix the whole original companion code label. -/
theorem generatedTenth_axis_lower_recovery_generator_companion (k : Fin 2) :
    golayLabelPermutation (generatedTenthAxisLowerRecoveryPermutation k) 110 = 110 := by
  apply golayLabelCoefficients_injective
  apply golayEncoder_injective
  rw [golayLabelPermutation_word,
    (generatedTenth_axis_lower_recovery_source_flags k).2.2]

/-- The two original source words as actual members of the entire permutation flag group. -/
def generatedTenthAxisLowerRecoveryFlagGenerator (k : Fin 2) :
    generatedTenthE7StandardFlagPermutationGroup :=
  ⟨generatedTenthAxisLowerRecoveryOctadGenerator k, by
    apply Prod.ext
    · exact generatedTenth_axis_lower_recovery_generator_pair k
    · exact generatedTenth_axis_lower_recovery_generator_companion k⟩

/-- Every source traversal word evaluated inside the entire actual flag group. -/
def generatedTenthAxisLowerRecoveryFlagWord (r : Fin 720) :
    generatedTenthE7StandardFlagPermutationGroup :=
  ((generatedTenthAxisLowerRecoveryTraversalWord r).map
    generatedTenthAxisLowerRecoveryFlagGenerator).prod

/-- Pure coordinate evaluation retains the order of every original source letter. -/
def generatedTenthAxisLowerRecoveryEvaluateWord (w : List (Fin 2)) : Fin 24 → Fin 24 :=
  w.foldr (fun k f i => generatedTenthAxisLowerRecoveryPermutationForward k (f i)) id

/-- All actual source products equal the coordinate evaluation of their original words. -/
theorem generatedTenth_axis_lower_recovery_word_evaluate (w : List (Fin 2)) (i : Fin 24) :
    (((w.map generatedTenthAxisLowerRecoveryFlagGenerator).prod).val.val.val i) =
      generatedTenthAxisLowerRecoveryEvaluateWord w i := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    simp only [List.map_cons, List.prod_cons]
    change (generatedTenthAxisLowerRecoveryPermutation k).val
      (((w.map generatedTenthAxisLowerRecoveryFlagGenerator).prod).val.val.val i) = _
    rw [ih, generatedTenth_axis_lower_recovery_source_forward]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
