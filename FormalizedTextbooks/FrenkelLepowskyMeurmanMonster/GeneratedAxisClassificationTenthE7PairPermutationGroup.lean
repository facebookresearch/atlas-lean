/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7CompanionCoverage

/-! The entire actual standard-octad and first-pair permutation group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire actual permutation stabilizer of the standard octad and its unordered first pair. -/
abbrev generatedTenthE7PairPermutationGroup :=
  MulAction.stabilizer generatedTenthE7OctadPermutationGroup generatedTenthE7OctadFirstPair

/-- The complete genuine pair group acts on all original Golay labels. -/
instance generatedTenthE7PairCodeAction :
    MulAction generatedTenthE7PairPermutationGroup (Fin 4096) :=
  MulAction.compHom (Fin 4096)
    (golayLabelActionHom.comp
      (generatedTenthE7OctadPermutationGroup.subtype.comp
        generatedTenthE7PairPermutationGroup.subtype))

/-- Every original first-pair coordinate is sent to one of its two actual coordinates. -/
theorem generatedTenth_e7_pair_permutation_coordinate
    (p : generatedTenthE7PairPermutationGroup) (i : Fin 2) :
    p.val.val.val (Fin.castAdd 22 i) = 0 ∨ p.val.val.val (Fin.castAdd 22 i) = 1 := by
  let j : Fin 8 := Fin.castAdd 6 i
  have hj : j ∈ generatedTenthE7OctadFirstPair.val := by
    fin_cases i <;> decide +kernel
  have hm : generatedTenthE7OctadPointPermutationHom p.val j ∈
      generatedTenthE7OctadFirstPair.val.map
        (generatedTenthE7OctadPointPermutationHom p.val).toEmbedding :=
    Finset.mem_map.mpr ⟨j, hj, rfl⟩
  have hp := congrArg Subtype.val p.property
  change generatedTenthE7OctadFirstPair.val.map
    (generatedTenthE7OctadPointPermutationHom p.val).toEmbedding =
      generatedTenthE7OctadFirstPair.val at hp
  rw [hp] at hm
  simp only [generatedTenthE7OctadFirstPair, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h
  · left
    apply Fin.ext
    exact congrArg (fun x : Fin 8 => x.val) h
  · right
    apply Fin.ext
    exact congrArg (fun x : Fin 8 => x.val) h

/-- Pointwise-octad permutations genuinely fix the complete first-pair object. -/
theorem generatedTenth_e7_pointwise_pair_mem (p : generatedNinthStandardOctadPointwise) :
    generatedTenthE7PointwiseOctadElement p ∈ generatedTenthE7PairPermutationGroup := by
  have he : generatedTenthE7OctadPointPermutationHom
      (generatedTenthE7PointwiseOctadElement p) = 1 := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    change (p.val.val (Fin.castAdd 16 i)).val = i.val
    exact congrArg (fun x : Fin 24 => x.val) (p.property i)
  apply Subtype.ext
  change generatedTenthE7OctadFirstPair.val.map
    (generatedTenthE7OctadPointPermutationHom
      (generatedTenthE7PointwiseOctadElement p)).toEmbedding =
        generatedTenthE7OctadFirstPair.val
  rw [he]
  exact Finset.map_refl

/-- Every member of the whole pointwise group is a genuine member of the whole pair group. -/
def generatedTenthE7PointwisePairElement (p : generatedNinthStandardOctadPointwise) :
    generatedTenthE7PairPermutationGroup :=
  ⟨generatedTenthE7PointwiseOctadElement p, generatedTenth_e7_pointwise_pair_mem p⟩

/-- The actual pointwise companion orbit is contained in the actual whole pair-group orbit. -/
theorem generatedTenth_e7_pointwise_companion_orbit_le_pair :
    MulAction.orbit generatedNinthStandardOctadPointwise (2306 : Fin 4096) ⊆
      MulAction.orbit generatedTenthE7PairPermutationGroup (2306 : Fin 4096) := by
  rintro d ⟨p, rfl⟩
  exact ⟨generatedTenthE7PointwisePairElement p, rfl⟩

/-- The entire genuine octad and pair permutation group has order11520. -/
theorem generatedTenth_e7_pair_permutation_group_card :
    Nat.card generatedTenthE7PairPermutationGroup = 11520 :=
  generatedTenth_e7_octad_pair_stabilizer_card _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
