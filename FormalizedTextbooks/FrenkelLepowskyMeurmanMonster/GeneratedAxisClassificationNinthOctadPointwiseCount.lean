/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadPointwiseOrbit

/-! Exactly sixteen genuine Golay permutations fix all standard-octad points. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Pointwise octad fixation embeds into the counted six-point stabilizer. -/
def generatedNinthStandardOctadInclusion (p : generatedNinthStandardOctadPointwise) :
    MulAction.stabilizer (golayPointStabilizer 5) (5 : Fin 24) := by
  refine ⟨⟨p.val, ?_⟩, ?_⟩
  · intro j hj
    let j₅ : Fin 5 := ⟨j.val, hj⟩
    have hJ : Fin.castAdd 2 j₅ = j := Fin.ext rfl
    have hI : Fin.castAdd 19 j₅ = (Fin.castAdd 16 ⟨j.val, by omega⟩ : Fin 24) := Fin.ext rfl
    rw [← hJ, golayBasePoints_firstFive, hI]
    exact p.property ⟨j.val, by omega⟩
  · change p.val.val (5 : Fin 24) = 5
    exact p.property 5

/-- The actual pointwise-octad inclusion retains the original permutation. -/
theorem generatedNinthStandardOctadInclusion_injective :
    Function.Injective generatedNinthStandardOctadInclusion := by
  intro p q h
  apply Subtype.ext
  exact congrArg (fun x => x.val.val) h

/-- No more than sixteen actual permutations fix the entire standard octad. -/
theorem generatedNinth_standard_octad_pointwise_card_le :
    Nat.card generatedNinthStandardOctadPointwise ≤ 16 := by
  rw [← generatedNinth_golay_five_octad_stabilizer_card]
  exact Nat.card_le_card_of_injective generatedNinthStandardOctadInclusion
    generatedNinthStandardOctadInclusion_injective

/-- The sixteen corrected source words are actual members of the pointwise octad group.
-/
def generatedNinthStandardOctadElement (j : Fin 16) : generatedNinthStandardOctadPointwise :=
  ⟨generatedNinthStandardOctadRepresentative j,
    generatedNinth_standard_octad_representative_fixed j⟩

/-- Distinct outside-coordinate images identify sixteen distinct actual subgroup elements. -/
theorem generatedNinthStandardOctadElement_injective :
    Function.Injective generatedNinthStandardOctadElement := by
  intro a b h
  have he := congrArg (fun p : generatedNinthStandardOctadPointwise => p.val.val 8) h
  change (generatedNinthStandardOctadRepresentative a).val 8 =
    (generatedNinthStandardOctadRepresentative b).val 8 at he
  rw [generatedNinth_standard_octad_representative_outside,
    generatedNinth_standard_octad_representative_outside] at he
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only [Fin.val_natAdd] at hv
  omega

/-- All sixteen original corrected words occur in the actual pointwise octad group. -/
theorem generatedNinth_standard_octad_pointwise_card_ge :
    16 ≤ Nat.card generatedNinthStandardOctadPointwise := by
  have h := Nat.card_le_card_of_injective generatedNinthStandardOctadElement
    generatedNinthStandardOctadElement_injective
  simpa only [Nat.card_fin] using h

/-- The whole actual standard-octad pointwise permutation group has order sixteen. -/
theorem generatedNinth_standard_octad_pointwise_card :
    Nat.card generatedNinthStandardOctadPointwise = 16 :=
  Nat.le_antisymm generatedNinth_standard_octad_pointwise_card_le
    generatedNinth_standard_octad_pointwise_card_ge

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
