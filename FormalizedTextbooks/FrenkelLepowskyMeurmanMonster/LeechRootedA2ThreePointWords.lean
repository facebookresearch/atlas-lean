/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismGeneration

/-! Actual array provenance and nine original strong generators of the three-point stabilizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

theorem leechRootedA2GeneratingLetter_apply (t : Fin 4) (i : Fin 24) :
    (golayGeneratingLetter t).val i = golayGeneratingLetterArray t i := by
  fin_cases t <;> rfl

theorem leechRootedA2GeneratingWord_apply (w : List (Fin 4)) (i : Fin 24) :
    (golayGeneratingWord w).val i = golayGeneratingWordArray w i := by
  induction w generalizing i with
  | nil => rfl
  | cons t w ih =>
    change (golayGeneratingLetter t).val ((golayGeneratingWord w).val i) = _
    rw [leechRootedA2GeneratingLetter_apply, ih]
    rfl

theorem leechRootedA2StrongAutomorphism_apply (s : Fin 14) (i : Fin 24) :
    (golayStrongAutomorphism s).val i = golayStrongForward s i := by
  rw [golayStrongAutomorphism, leechRootedA2GeneratingWord_apply, golayStrongWords_certificate]

theorem leechRootedA2StrongAutomorphism_inverse_apply (s : Fin 14) (i : Fin 24) :
    (golayStrongAutomorphism s).val.symm i = golayStrongInverse s i := by
  apply (golayStrongAutomorphism s).val.injective
  rw [Equiv.apply_symm_apply, leechRootedA2StrongAutomorphism_apply,
    (golayStrong_inverse_certificate s i).1]

theorem leechRootedA2StrongLetter_apply (t : Fin 28) (i : Fin 24) :
    (golayStrongLetter t).val i = golayStrongLetterArray t i := by
  unfold golayStrongLetter golayStrongLetterArray
  split_ifs
  · exact leechRootedA2StrongAutomorphism_apply _ i
  · exact leechRootedA2StrongAutomorphism_inverse_apply _ i

theorem leechRootedA2StrongWord_apply (w : List (Fin 28)) (i : Fin 24) :
    (golayStrongWord w).val i = golayStrongWordArray w i := by
  induction w generalizing i with
  | nil => rfl
  | cons t w ih =>
    change (golayStrongLetter t).val ((golayStrongWord w).val i) = _
    rw [leechRootedA2StrongLetter_apply, ih]
    rfl

/-- Exactly nine frozen strong generators fix the first three physical coordinates. -/
def leechRootedA2ThreePointStrongIndex : Fin 9 → Fin 14 := ![4, 6, 7, 8, 9, 10, 11, 12, 13]

/-- Their original physical arrays fix all three base coordinates. -/
theorem leechRootedA2ThreePointStrong_fixed : ∀ j : Fin 9, ∀ k : Fin 3,
    golayStrongForward (leechRootedA2ThreePointStrongIndex j) (Fin.castAdd 21 k) =
      Fin.castAdd 21 k := by
  decide +kernel

/-- Every deeper original transversal word uses only these nine generators and their inverses. -/
theorem leechRootedA2ThreePointStrong_word_certificate : ∀ r : Fin 129,
    3 ≤ (golayStabilizerRepLevel r).val →
      ∀ t ∈ golayStabilizerStrongWords r, ∃ j : Fin 9,
        t.val = (leechRootedA2ThreePointStrongIndex j).val ∨
          t.val = (leechRootedA2ThreePointStrongIndex j).val + 14 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
