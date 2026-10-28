/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Reduction of the actual signed-octad and odd lifts to the source dictionary. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortSpinDictionary

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Negation is trivial in the actual quotient by twice the Leech lattice. -/
theorem leechModTwo_neg_self (u : LeechModTwo) : -u = u := by
  apply neg_eq_of_add_eq_zero_left
  simpa only [two_nsmul] using leechModTwo_two_smul u

theorem leechModTwo_two_zsmul (u : LeechModTwo) : (2 : ℤ) • u = 0 := by
  rw [← Int.cast_smul_eq_zsmul (ZMod 2)]
  have hn : ((2 : ℤ) : ZMod 2) = 0 := by decide
  rw [hn, zero_smul]

/-- Complementing a normalized source code vector changes its class by Ω. -/
theorem leechTwiceCodeWord_class (d : Fin 4096) :
    leechReduction (leechTwiceCodeWordLift d) =
      leechReduction (leechSourceCodeWordLift d) +
        (if golayMaskWeight (golayEncodedMask d.val) % 8 = 0 then (0 : ℤ) else 1) •
          leechReduction (leechTwiceCodeWordLift 2048) := by
  by_cases h : golayMaskWeight (golayEncodedMask d.val) % 8 = 0
  · simp [leechSourceCodeWordLift, h]
  · simp only [leechSourceCodeWordLift, h, ite_false, one_smul]
    rw [map_sub, sub_eq_add_neg, leechModTwo_neg_self]
    rw [add_assoc, add_comm (leechReduction (leechTwiceCodeWordLift d)), ← add_assoc]
    simp [← two_nsmul, leechModTwo_two_smul]

/-- A signed octad's class is its normalized code class plus its negative
cocode class and the parity of half its negative-position count. -/
theorem griessOctad_source_class (d : Fin 759) (e : Fin 64) :
    griessShortClass (Sum.inr (Sum.inl (d, e))) =
      leechReduction (leechSourceCodeWordLift (golayOctadLabel d)) +
        leechReduction (leechCocodeLift (griessOctadNegativeInteger d e)) +
          ((trialityBitWeight8 (trialityEvenMask e) / 2 : ℕ) : ℤ) •
            leechReduction (leechTwiceCodeWordLift 2048) := by
  rw [griessShortClass, griessOctad_source_lift, map_sub, map_add, map_zsmul,
    sub_eq_add_neg, leechModTwo_neg_self]
  have hw : golayMaskWeight (golayEncodedMask (golayOctadLabel d).val) = 8 := by
    rw [← golayMaskSupport_card]
    exact golayOctad_support_card d
  simp only [leechSourceCodeWordLift, hw, Nat.reduceMod, ite_true]

/-- An odd short class is its singleton cocode class plus its normalized code
class, with the explicit Ω correction from weight and the selected bit. -/
theorem griessOdd_source_class (d : Fin 2048) (j : Fin 24) :
    griessShortClass (Sum.inr (Sum.inr (d, j))) =
      leechReduction (leechSourceCodeWordLift ⟨d.val, by omega⟩) +
        leechReduction (leechCocodeLift (Pi.single j 1)) +
          ((if golayMaskWeight (golayEncodedMask d.val) % 8 = 0 then (0 : ℤ) else 1) +
            (if (golayEncodedMask d.val).testBit j.val then (1 : ℤ) else 0)) •
              leechReduction (leechTwiceCodeWordLift 2048) := by
  rw [griessShortClass, griessOdd_source_lift, map_add, map_sub, map_zsmul,
    map_sub, map_zsmul, leechModTwo_two_zsmul, sub_zero,
    sub_eq_add_neg, leechModTwo_neg_self, leechTwiceCodeWord_class, add_smul]
  exact (show ∀ a b c f : LeechModTwo, a + (b + c) + f = b + a + (c + f) from
    by intros; abel) _ _ _ _

/-- The signed octad coordinate computation reduces to the normalized code
word coordinate formula and the explicit cocode syndrome. -/
theorem griessOctad_source_coordinates (d : Fin 759) (e : Fin 64) :
    leechHyperbolicCoordinates (griessShortClass (Sum.inr (Sum.inl (d, e)))) =
      leechHyperbolicCoordinates (leechReduction
        (leechSourceCodeWordLift (golayOctadLabel d))) +
          binaryCocodeEmbedding (golaySyndrome (integerParity (griessOctadNegativeInteger d e))) +
            ((trialityBitWeight8 (trialityEvenMask e) / 2 : ℕ) : ℤ) •
              Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1 := by
  rw [griessOctad_source_class, map_add, map_add, map_zsmul,
    leechCocodeLift_coordinates, leechTwiceCodeWordLift_omega,
    leechSourceFrameLift_hyperbolic]

/-- The singleton cocode syndrome in physical coordinate j. -/
theorem golaySyndrome_singleton (j : Fin 24) :
    golaySyndrome (integerParity (Pi.single j 1)) =
      fun k => (golayGeneratorBit k j : ZMod 2) := by
  ext k
  simp [golaySyndrome, integerParity, Pi.single_apply]

/-- The odd vector coordinate computation reduces to the normalized code word
formula and the physical singleton syndrome, with the exact Ω correction. -/
theorem griessOdd_source_coordinates (d : Fin 2048) (j : Fin 24) :
    leechHyperbolicCoordinates (griessShortClass (Sum.inr (Sum.inr (d, j)))) =
      leechHyperbolicCoordinates (leechReduction
        (leechSourceCodeWordLift ⟨d.val, by omega⟩)) +
          binaryCocodeEmbedding (fun k => (golayGeneratorBit k j : ZMod 2)) +
            ((if golayMaskWeight (golayEncodedMask d.val) % 8 = 0 then (0 : ℤ) else 1) +
              (if (golayEncodedMask d.val).testBit j.val then (1 : ℤ) else 0)) •
                Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1 := by
  rw [griessOdd_source_class, map_add, map_add, map_zsmul,
    leechCocodeLift_coordinates, golaySyndrome_singleton,
    leechTwiceCodeWordLift_omega, leechSourceFrameLift_hyperbolic]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
