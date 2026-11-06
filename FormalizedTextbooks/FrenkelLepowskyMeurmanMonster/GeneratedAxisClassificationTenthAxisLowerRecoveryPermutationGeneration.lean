/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationInverseTree

/-! Complete actual source generation of the whole 720-element permutation flag group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- All 720 full source words have the stored entire original 24-coordinate actions. -/
theorem generatedTenth_axis_lower_recovery_traversal_coordinates : ∀ r : Fin 720,
    generatedTenthAxisLowerRecoveryEvaluateWord
      (generatedTenthAxisLowerRecoveryTraversalWord r) =
      generatedTenthAxisLowerRecoveryTraversalForward r := by
  intro r
  have hblocks : ∀ b : Fin 16, ∀ u : Fin 45,
      generatedTenthAxisLowerRecoveryEvaluateWord
        (generatedTenthAxisLowerRecoveryTraversalWord ⟨45 * b.val + u.val, by omega⟩) =
          generatedTenthAxisLowerRecoveryTraversalForward ⟨45 * b.val + u.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_00
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_01
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_02
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_03
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_04
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_05
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_06
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_07
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_08
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_09
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_10
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_11
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_12
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_13
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_14
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_15
  let b : Fin 16 := ⟨r.val / 45, by omega⟩
  let u : Fin 45 := ⟨r.val % 45, Nat.mod_lt _ (by decide)⟩
  have hr : (⟨45 * b.val + u.val, by omega⟩ : Fin 720) = r := by
    apply Fin.ext
    dsimp only [b, u]
    omega
  have h := hblocks b u
  simpa only [hr] using h

/-- Every retained source permutation is distinct; all 720 original entries are checked. -/
theorem generatedTenth_axis_lower_recovery_traversal_injective :
    Function.Injective generatedTenthAxisLowerRecoveryTraversalForward :=
  generatedTenth_axis_lower_recovery_traversal_injective_from_tree

/-- Every actual flag word retains its complete source coordinate table. -/
theorem generatedTenth_axis_lower_recovery_flag_word_coordinate (r : Fin 720) (i : Fin 24) :
    (generatedTenthAxisLowerRecoveryFlagWord r).val.val.val i =
      generatedTenthAxisLowerRecoveryTraversalForward r i := by
  rw [generatedTenthAxisLowerRecoveryFlagWord,
    generatedTenth_axis_lower_recovery_word_evaluate,
    generatedTenth_axis_lower_recovery_traversal_coordinates]

/-- All 720 genuine source flag words are distinct in the entire actual flag group. -/
theorem generatedTenth_axis_lower_recovery_flag_word_injective :
    Function.Injective generatedTenthAxisLowerRecoveryFlagWord := by
  intro r s h
  apply generatedTenth_axis_lower_recovery_traversal_injective
  funext i
  have hh := congrArg (fun p : generatedTenthE7StandardFlagPermutationGroup =>
    p.val.val.val i) h
  simpa only [generatedTenth_axis_lower_recovery_flag_word_coordinate] using hh

/-- The complete original source traversal covers the entire actual 720-element flag group. -/
theorem generatedTenth_axis_lower_recovery_flag_word_surjective :
    Function.Surjective generatedTenthAxisLowerRecoveryFlagWord := by
  apply ((Nat.bijective_iff_injective_and_card
    generatedTenthAxisLowerRecoveryFlagWord).mpr ?_).surjective
  refine ⟨generatedTenth_axis_lower_recovery_flag_word_injective, ?_⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_fin,
    generatedTenth_e7_standard_flag_permutation_card]

/-- The two genuine original source flag generators generate the entire actual flag group. -/
theorem generatedTenth_axis_lower_recovery_flag_generation
    (S : Subgroup generatedTenthE7StandardFlagPermutationGroup)
    (hgen : ∀ k : Fin 2, generatedTenthAxisLowerRecoveryFlagGenerator k ∈ S) : S = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨r, rfl⟩ := generatedTenth_axis_lower_recovery_flag_word_surjective p
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hg
  exact hgen k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
