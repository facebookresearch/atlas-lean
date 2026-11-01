/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNormalization
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialCodeCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairSource

/-! Original code transforms and all-one normalization determine actual odd-short line transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The genuine encoder gives exactly the integer physical sign of a code coordinate. -/
theorem generatedSixth_integer_encoder_sign (d : Fin 4096) (i : Fin 24) :
    nortonUIntegerSign (golayEncoder (golayLabelCoefficients d) i) =
      (if (golayEncodedMask d.val).testBit i.val then (-1 : ℤ) else 1) := by
  have he : golayEncoder (golayLabelCoefficients d) i =
      if (golayEncodedMask d.val).testBit i.val then 1 else 0 := by
    apply ZMod.val_injective
    cases hb : (golayEncodedMask d.val).testBit i.val <;>
      simpa [hb, show (1 : ZMod 2).val = 1 by decide] using golayLabelEncoder_match d i
  rw [he]
  cases hb : (golayEncodedMask d.val).testBit i.val <;> rfl

/-- Integer binary signs multiply exactly under addition of the full binary phase. -/
theorem generatedSixth_integer_sign_add (a b : ZMod 2) :
    nortonUIntegerSign (a + b) = nortonUIntegerSign a * nortonUIntegerSign b := by
  apply Int.cast_injective (α := ℝ)
  simp only [Int.cast_mul, nortonUIntegerSign_real, qSign_add]

/-- Removing the all-one coordinate retains its exact physical global sign. -/
theorem generatedSixth_monomial_odd_encoder_transport (k : Fin 4) (f : Fin 512)
    (hs : (generatedSixthMonomialOddCode (generatedSixthMonomialOddSourceFamily k f)).val =
      (generatedSixthMonomialOddFullSourceCode k f).val % 2048) (i : Fin 24) :
    golayEncoder (golayLabelCoefficients
      ⟨(generatedSixthMonomialOddCode (generatedSixthMonomialOddSourceFamily k f)).val,
        by omega⟩)
      (generatedSixthMonomialPairInput k i) =
    golayEncoder (golayLabelCoefficients ⟨(generatedSixthMonomialOddCode f).val, by omega⟩) i +
      (if (generatedSixthMonomialOddFullSourceCode k f).val.testBit 11 then 1 else 0) := by
  have hl := generatedSixth_monomial_low_code (generatedSixthMonomialOddFullSourceCode k f)
  have hd : generatedSixthMonomialLowCode (generatedSixthMonomialOddFullSourceCode k f) =
      ⟨(generatedSixthMonomialOddCode (generatedSixthMonomialOddSourceFamily k f)).val,
        by omega⟩ := Fin.ext hs.symm
  rw [hd, generatedSixth_monomial_odd_full_source] at hl
  have he := congrFun (congrArg golayEncoder hl) (generatedSixthMonomialPairInput k i)
  rw [map_add, Pi.add_apply] at he
  have ho : golayEncoder
      (if (generatedSixthMonomialOddFullSourceCode k f).val.testBit 11 then
        (Pi.single 11 1 : SpinIndex) else 0) (generatedSixthMonomialPairInput k i) =
      (if (generatedSixthMonomialOddFullSourceCode k f).val.testBit 11 then 1 else 0) := by
    split <;> simp_all [golay_all_one]
  rw [ho] at he
  change _ + _ = golayEncoder
    ((representativeMatrix (generatedSixthMonomialMaskCoordinateRows k)) *ᵥ
      golayLabelCoefficients ⟨(generatedSixthMonomialOddCode f).val, by omega⟩)
    (sixthFrameOrbitSpatialInput (Fin.natAdd 10 (Fin.castAdd 2 k)) i) at he
  rw [generatedSixth_monomial_code_coordinates] at he
  have hc : ∀ c : ZMod 2, c + c = 0 := by decide +kernel
  rw [← he, add_assoc, hc, add_zero]

/-- The actual distinguished-coordinate permutation and normalized code give a signed line image. -/
theorem generatedSixth_monomial_odd_source_permutation (k : Fin 4) (f : Fin 512)
    (hs : (generatedSixthMonomialOddCode (generatedSixthMonomialOddSourceFamily k f)).val =
      (generatedSixthMonomialOddFullSourceCode k f).val % 2048) (j : Fin 24) :
    griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2
      (Sum.inr (Sum.inr
        (generatedSixthMonomialOddCode (generatedSixthMonomialOddSourceFamily k f),
          generatedSixthMonomialPairInput k j))) =
      Sum.inr (Sum.inr (generatedSixthMonomialOddCode f, j)) := by
  apply generatedSixth_short_permutation_of_vector
  have hh (i : Fin 24) := generatedSixth_monomial_odd_encoder_transport k f hs i
  have hp (i : Fin 24) := congrArg nortonUIntegerSign (hh i)
  simp_rw [generatedSixth_integer_sign_add] at hp
  simp only [generatedSixth_integer_encoder_sign] at hp
  have hi (i : Fin 24) : generatedSixthMonomialPairInput k i =
      generatedSixthMonomialPairInput k j ↔ i = j :=
    (generatedSixth_monomial_pair_input_injective k).eq_iff
  by_cases h : (generatedSixthMonomialOddFullSourceCode k f).val.testBit 11 = true
  · right
    funext i
    rw [generatedSixth_monomial_physical_apply]
    change griessShortVector _ (generatedSixthMonomialPairInput k i) = _
    simp only [griessShortVector, griessShortIntegral, hp i, h, ite_true,
      nortonUIntegerSign, one_ne_zero, ite_false, mul_neg_one, hi i, Pi.neg_apply]
    push_cast
    ring
  · left
    funext i
    rw [generatedSixth_monomial_physical_apply]
    change griessShortVector _ (generatedSixthMonomialPairInput k i) = _
    simp only [griessShortVector, griessShortIntegral, hp i, h, Bool.false_eq_true,
      ite_false, nortonUIntegerSign, ite_true, mul_one, hi i]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
