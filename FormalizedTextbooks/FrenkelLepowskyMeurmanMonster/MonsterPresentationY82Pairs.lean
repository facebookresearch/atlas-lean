/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual pair permutation and central phases of the explicit source y82 candidate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82PairConjugation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The source code character on the two physical coordinates of a pair. -/
def monsterY82PairCharacter (p : Fin 276) : ZMod 2 :=
  golayEncoder monsterSourceY82Code (griessCoordinatePair p).1 +
    golayEncoder monsterSourceY82Code (griessCoordinatePair p).2

/-- The actual pair color changes precisely when the two code signs differ. -/
def monsterY82PairColor (s : Fin 2) (p : Fin 276) : Fin 2 :=
  if monsterY82PairCharacter p = 0 then s else (Equiv.swap 0 1) s

/-- The pair color change is addition of the exact binary character. -/
theorem monsterY82PairColor_val (s : Fin 2) (p : Fin 276) :
    ((monsterY82PairColor s p).val : ZMod 2) =
      (s.val : ZMod 2) + monsterY82PairCharacter p := by
  have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
  have hs : ∀ s : Fin 2, s = 0 ∨ s = 1 := by decide +kernel
  rcases hc (monsterY82PairCharacter p) with h | h
  · simp [monsterY82PairColor, h]
  · have h11 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
    rcases hs s with rfl | rfl <;> simp [monsterY82PairColor, h, h11]

/-- The color change is an involution for each fixed physical pair. -/
theorem monsterY82PairColor_double (s : Fin 2) (p : Fin 276) :
    monsterY82PairColor (monsterY82PairColor s p) p = s := by
  by_cases h : monsterY82PairCharacter p = 0
  · simp [monsterY82PairColor, h]
  · simp [monsterY82PairColor, h]

/-- A preferred actual pair lift has these coordinates and central coefficient zero. -/
theorem monsterY82PairLift (s : Fin 2) (p : Fin 276) :
    griessShortQ (Sum.inl (s, p)) = monsterY82CoordinateLift
      ((s.val : ZMod 2) • monsterSpinOmegaVector) (griessPairSyndrome p) 0 := by
  apply monsterY82CoordinateLift_eq
  · exact griessPairQ_translation_color s p
  · exact griessPairQ_modulation s p
  · exact griessShortQ_coeff _

/-- The actual normalizer sends each preferred pair lift to its exact signed color change. -/
theorem monsterSourceY82Image_pair (s : Fin 2) (p : Fin 276) :
    monsterSourceY82Image (griessShortQ (Sum.inl (s, p))) =
      qCentral (monsterY82PairCharacter p) *
        griessShortQ (Sum.inl (monsterY82PairColor s p, p)) := by
  rw [monsterY82PairLift, monsterSourceY82Image_even _ _ _ (griessPairSyndrome_omega p),
    griessPairSyndrome_dot, monsterY82PairLift, monsterY82CoordinateLift_central_mul,
    monsterY82PairColor_val, zero_add, add_zero]
  rfl

/-- The signed pair phase belongs to the actual local fiber, rather than an abstract action. -/
theorem monsterSourceY82_pair_phase (s : Fin 2) (p : Fin 276) :
    localShortPhase monsterSourceY82Fiber (Sum.inl (s, p)) =
      monsterY82PairCharacter p := by
  change toAdd (spinConjugation monsterSourceY82Spin
    (griessShortQ (Sum.inl (s, p)))).coeff = _
  rw [monsterSourceY82Spin_conjugation, monsterSourceY82Image_pair, qCentral_mul_coeff,
    griessShortQ_coeff, add_zero]

/-- Actual preferred short Q bases determine their catalogue indices. -/
theorem monsterY82ShortQ_base_injective :
    Function.Injective (fun r : GriessShortIndex => (griessShortQ r).base) := by
  intro r s h
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  exact congrArg Multiplicative.toAdd h

/-- The genuine Leech sign has the same pair color permutation as its checked spin lift. -/
theorem monsterSourceY82_pair_permutation (s : Fin 2) (p : Fin 276) :
    griessShortPermutation monsterSourceY82Isometry (Sum.inl (s, p)) =
      Sum.inl (monsterY82PairColor s p, p) := by
  apply monsterY82ShortQ_base_injective
  have h := griessShortQ_image_base monsterSourceY82Fiber (Sum.inl (s, p))
  change (spinConjugation monsterSourceY82Spin (griessShortQ (Sum.inl (s, p)))).base =
    (griessShortQ (griessShortPermutation monsterSourceY82Isometry (Sum.inl (s, p)))).base at h
  rw [monsterSourceY82Spin_conjugation, monsterSourceY82Image_pair, qCentral_mul_base] at h
  exact h.symm

/-- The actual short-vector representation has the source pair sign and color change. -/
theorem monsterSourceY82_pair_operator (x : GriessShortIndex → ℝ) (s : Fin 2) (p : Fin 276) :
    localShortOperator monsterSourceY82Fiber x (Sum.inl (s, p)) =
      qSign (monsterY82PairCharacter p) * x (Sum.inl (monsterY82PairColor s p, p)) := by
  have h := localShortOperator_image monsterSourceY82Fiber x
    (Sum.inl (monsterY82PairColor s p, p))
  change localShortOperator monsterSourceY82Fiber x
      (griessShortPermutation monsterSourceY82Isometry
        (Sum.inl (monsterY82PairColor s p, p))) = _ at h
  rw [monsterSourceY82_pair_permutation, monsterY82PairColor_double,
    monsterSourceY82_pair_phase] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
