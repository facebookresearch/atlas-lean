/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialWords

/-! Exact original signed monomial spin action of every word in the two source permutations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The original spin letter, before any fourth-axis correction. -/
def generatedFourthMonomialSpinLetter (l : Fin 2 × Bool) : SpinHolomorph :=
  if l.2 then (monsterSourcePermutationSpin l.1)⁻¹ else monsterSourcePermutationSpin l.1

/-- Pullback of a spin label by a genuine signed source permutation letter. -/
def generatedFourthMonomialPullLetter (l : Fin 2 × Bool) (t : SpinIndex) : SpinIndex :=
  if l.2 then monsterSourcePermutationCode l.1 t
  else (monsterSourcePermutationCode l.1).symm t

/-- The literal original Parker phase of the pullback letter. -/
def generatedFourthMonomialPullPhase (l : Fin 2 × Bool) (t : SpinIndex) : ZMod 2 :=
  monsterMonomialQuadratic (monsterSourcePermutationPhaseData l.1)
    (if l.2 then t else (monsterSourcePermutationCode l.1).symm t)

/-- Each original letter has exactly the claimed label pullback and original signed phase. -/
theorem generatedFourth_monomial_spin_letter_apply (l : Fin 2 × Bool)
    (f : SpinSpace) (t : SpinIndex) :
    (generatedFourthMonomialSpinLetter l).val f t =
      qSign (generatedFourthMonomialPullPhase l t) *
        f (generatedFourthMonomialPullLetter l t) := by
  rcases l with ⟨i, b⟩
  cases b <;> rfl

/-- Signed pullback through a literal product of the two original source spin operators. -/
def generatedFourthMonomialWordPull : List (Fin 2 × Bool) → SpinIndex → ZMod 2 × SpinIndex
  | [], t => (0, t)
  | l :: w, t =>
    let r := generatedFourthMonomialWordPull w (generatedFourthMonomialPullLetter l t)
    (generatedFourthMonomialPullPhase l t + r.1, r.2)

/-- Exact signed coordinate action of every actual original source spin word. -/
theorem generatedFourth_monomial_spin_word_apply (w : List (Fin 2 × Bool))
    (f : SpinSpace) (t : SpinIndex) :
    ((w.map generatedFourthMonomialSpinLetter).prod).val f t =
      qSign (generatedFourthMonomialWordPull w t).1 *
        f (generatedFourthMonomialWordPull w t).2 := by
  induction w generalizing t with
  | nil => simp [generatedFourthMonomialWordPull, qSign_zero]
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons]
    change (generatedFourthMonomialSpinLetter l).val
      (((w.map generatedFourthMonomialSpinLetter).prod).val f) t = _
    rw [generatedFourth_monomial_spin_letter_apply, ih]
    simp only [generatedFourthMonomialWordPull, qSign_add, mul_assoc]

/-- The ordinary spin projection of the genuine local fiber group. -/
def generatedFourthMonomialSpinProjection : localFiberSubgroup →* SpinHolomorph where
  toFun f := f.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The literal full fiber word has exactly the original spin product. -/
theorem generatedFourth_monomial_spin_projection (k : Fin 4) :
    (generatedFourthMonomialFiber k).val.1 =
      ((generatedFourthMonomialWord k).map generatedFourthMonomialSpinLetter).prod := by
  change generatedFourthMonomialSpinProjection (generatedFourthMonomialFiber k) = _
  rw [generatedFourthMonomialFiber, map_list_prod]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro l _
  rcases l with ⟨i, b⟩
  cases b with
  | false => rfl
  | true =>
    change generatedFourthMonomialSpinProjection ((monsterSourcePermutationFiber i)⁻¹) = _
    rw [map_inv]
    rfl

/-- The four genuine local lifts retain the exact original signed spin pullback. -/
theorem generatedFourth_monomial_spin_apply (k : Fin 4) (f : SpinSpace) (t : SpinIndex) :
    (generatedFourthMonomialFiber k).val.1.val f t =
      qSign (generatedFourthMonomialWordPull (generatedFourthMonomialWord k) t).1 *
        f (generatedFourthMonomialWordPull (generatedFourthMonomialWord k) t).2 := by
  rw [generatedFourth_monomial_spin_projection]
  exact generatedFourth_monomial_spin_word_apply _ f t

/-- Literal extraspecial translation coordinates of four candidate full-axis corrections. -/
def generatedFourthMonomialCorrectionTranslation : Fin 4 → Fin 4096 := ![385, 55, 258, 305]

/-- Literal modulation coordinates of the same four candidate full-axis corrections. -/
def generatedFourthMonomialCorrectionModulation : Fin 4 → Fin 4096 := ![1312, 1030, 1570, 1324]

/-- Actual extraspecial correction elements with central coordinate zero. -/
def generatedFourthMonomialCorrection (k : Fin 4) : Q :=
  ⟨ofAdd (Fin.append
    (golayLabelCoefficients (generatedFourthMonomialCorrectionTranslation k))
    (golayLabelCoefficients (generatedFourthMonomialCorrectionModulation k))), 1⟩

/-- Four genuine corrected local lifts, whose fixation requires separate coordinate certificates. -/
def generatedFourthMonomialCorrectedFiber (k : Fin 4) : localFiberSubgroup :=
  localFiberIncl (generatedFourthMonomialCorrection k) * generatedFourthMonomialFiber k

/-- The genuine extraspecial corrections leave every actual physical component unchanged. -/
theorem generatedFourth_monomial_corrected_spatial (k : Fin 4) :
    (generatedFourthMonomialCorrectedFiber k).val.2 = (generatedFourthMonomialFiber k).val.2 :=
  one_mul _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
