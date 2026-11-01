/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceScalarFree
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineSignedWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineTransportAction

/-! Genuine spatial free-word identities for the eleven proposed Ninth lower generators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Embed the two original permutation letters in the primitive source alphabet. -/
def generatedNinthLowerSpinPermutationEmbed (l : Fin 2 × Bool) :
    GeneratedNinthLowerSpinLetter := (⟨l.1.val + 12, by omega⟩, l.2)

/-- Original primitive word for the complete actual spatial transport. -/
def generatedNinthLowerSpinTransportWord : List GeneratedNinthLowerSpinLetter :=
  [(12, true), (12, true), (12, true), (13, false), (12, false), (12, false),
    (13, false), (12, false), (13, false), (14, true), (12, true), (13, false),
    (12, false), (12, false), (12, false), (13, false), (12, true), (13, false),
    (12, true), (13, false), (12, false), (12, false), (13, false), (12, false),
    (12, false), (5, false)]

/-- The original primitive macro for a positive selected-section generator. -/
def generatedNinthLowerSpinSectionMacro (k : Fin 18) :
    List GeneratedNinthLowerSpinLetter :=
  if h : k.val < 12 then [(⟨k.val, by omega⟩, false)]
  else if h' : k.val < 17 then
    (generatedNinthAffineSelectedWord ⟨k.val - 12, by omega⟩).map
      generatedNinthLowerSpinPermutationEmbed
  else [(14, false)]

/-- Signed section macros reverse and invert the entire original primitive word. -/
def generatedNinthLowerSpinSignedSectionMacro (l : Fin 18 × Bool) :
    List GeneratedNinthLowerSpinLetter :=
  if l.2 then generatedNinthLowerSpinInverseWord (generatedNinthLowerSpinSectionMacro l.1)
  else generatedNinthLowerSpinSectionMacro l.1

/-- The actual spatial component homomorphism on compatible local fibers. -/
def generatedNinthLowerSpinSpatialProjection : localFiberSubgroup →* leechIsomSubgroup :=
  (MonoidHom.snd _ _).comp localFiberSubgroup.subtype

/-- Evaluate a primitive word in the genuine spatial components of its local fibers. -/
def generatedNinthLowerSpinSpatialWord (w : List GeneratedNinthLowerSpinLetter) :
    leechIsomSubgroup :=
  (w.map (fun l => generatedNinthLowerSpinSpatialProjection
    (generatedNinthLowerSpinFiberLetter l))).prod

/-- The literal flattened source words retain the original transport and all section macros. -/
theorem generatedNinth_lower_spin_spatial_word_expansion : ∀ i : Fin 11,
    generatedNinthLowerSpinSourceWord i =
      generatedNinthLowerSpinInverseWord generatedNinthLowerSpinTransportWord ++
        (generatedNinthAffineLowerSourceWord i).flatMap
          generatedNinthLowerSpinSignedSectionMacro ++ generatedNinthLowerSpinTransportWord := by
  decide +kernel

/-- No selected-section scalar sign occurs in the eleven original lower words. -/
theorem generatedNinth_lower_spin_section_scalar_free : ∀ i : Fin 11,
    (generatedNinthAffineLowerSourceWord i).all (fun l => l.1.val != 11) = true := by
  decide +kernel

/-- Every selected-section letter used in a lower word avoids the unused scalar sign. -/
theorem generatedNinth_lower_spin_section_letter_ne_scalar (i : Fin 11) (l : Fin 18 × Bool)
    (hl : l ∈ generatedNinthAffineLowerSourceWord i) : l.1.val ≠ 11 := by
  have h := List.all_eq_true.mp (generatedNinth_lower_spin_section_scalar_free i) l hl
  simpa using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
