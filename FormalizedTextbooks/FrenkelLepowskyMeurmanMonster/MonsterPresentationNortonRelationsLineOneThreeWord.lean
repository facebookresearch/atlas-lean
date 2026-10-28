/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A bounded concrete source-word transport for the independent distance-two line seed. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLineOneThreeCentralizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsYAllConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImage

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- A full source word using only the already bound permutation, xi, and source Y factors. -/
noncomputable def monsterNortonLineOneThreeTransportWord : G :=
  xiSpinGenerated * (monsterSourcePermutationGenerated 1)⁻¹ * xiSpinGenerated *
    ((monsterSourcePermutationGenerated 0)⁻¹) ^ 2 *
      (y555NortonActualY 16 0)⁻¹ * monsterSourcePermutationGenerated 1 * xiSpinGenerated

/-- The full actual central-corrected Q image through those source factors. -/
noncomputable def monsterNortonLineOneThreeTransportImage (q : Q) : Q :=
  monsterNortonXiQImage (monsterNortonPermutationInverseImage 1
    (monsterNortonXiQImage (monsterNortonPermutationInverseImage 0
      (monsterNortonPermutationInverseImage 0 (monsterNortonYImage 16
        (monsterSourcePermutationImage 1 (monsterNortonXiQImage q)))))))

private theorem conjugate_mul {K : Type*} [Group K] (a b q : K) :
    (a * b) * q * (a * b)⁻¹ = a * (b * q * b⁻¹) * a⁻¹ := by group

private theorem permutation_conjugation (k : Fin 2) (q : Q) :
    monsterSourcePermutationGenerated k * qIntoGenerated q *
      (monsterSourcePermutationGenerated k)⁻¹ =
        qIntoGenerated (monsterSourcePermutationImage k q) := by
  have h := monsterFiberGenerated_conjugate_Q (monsterSourcePermutationFiber k) q
  change _ = qIntoGenerated (spinConjugation (monsterSourcePermutationSpin k) q) at h
  rw [monsterSourcePermutationSpin_conjugation] at h
  exact h

private theorem permutation_inverse_conjugation (k : Fin 2) (q : Q) :
    (monsterSourcePermutationGenerated k)⁻¹ * qIntoGenerated q *
      ((monsterSourcePermutationGenerated k)⁻¹)⁻¹ =
        qIntoGenerated (monsterNortonPermutationInverseImage k q) := by
  have h := monsterFiberGenerated_conjugate_Q ((monsterSourcePermutationFiber k)⁻¹) q
  change _ = qIntoGenerated (spinConjugation (monsterSourcePermutationSpin k)⁻¹ q) at h
  rw [monsterNortonPermutationInverseImage_eq] at h
  exact h

private theorem y16_square : (y555NortonActualY 16 0) ^ 2 = 1 := by
  have h : (sourceQCode 16 0) ^ 2 = 1 := by
    rw [pow_two]
    apply NormalizedCocycleExtension.Extension.ext
    · apply toAdd.injective
      change (fun j : Fin 24 => toAdd (sourceQCode 16 0 * sourceQCode 16 0).base j) =
        (fun _ : Fin 24 => (0 : ZMod 2))
      decide +kernel
    · apply toAdd.injective
      change toAdd (sourceQCode 16 0 * sourceQCode 16 0).coeff = (0 : ZMod 2)
      decide +kernel
  have hg := congrArg qIntoGenerated h
  rw [map_pow, map_one] at hg
  change (sourceGeneratedCode 16 0) ^ 2 = 1 at hg
  rw [y555NortonActualY_word, conj_pow, hg, mul_one, mul_inv_cancel]

private theorem y16_inverse_conjugation (q : Q) :
    (y555NortonActualY 16 0)⁻¹ * qIntoGenerated q *
      ((y555NortonActualY 16 0)⁻¹)⁻¹ = qIntoGenerated (monsterNortonYImage 16 q) := by
  have he : (y555NortonActualY 16 0)⁻¹ = y555NortonActualY 16 0 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, y16_square])
  rw [he]
  exact monsterNortonYAllWord_conjugation 16 q

/-- The displayed Q image is the genuine conjugation by the entire actual source word. -/
theorem monsterNortonLineOneThreeTransportWord_conjugation (q : Q) :
    monsterNortonLineOneThreeTransportWord * qIntoGenerated q *
      monsterNortonLineOneThreeTransportWord⁻¹ =
        qIntoGenerated (monsterNortonLineOneThreeTransportImage q) := by
  rw [monsterNortonLineOneThreeTransportWord, pow_two]
  simp only [conjugate_mul, xiSpinGenerated_conjugation, permutation_conjugation,
    permutation_inverse_conjugation, y16_inverse_conjugation]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check all twenty-four genuine binary coordinates through the full phase-correct source word.
/-- This concrete word transports the common four-point binary class to the actual all-one class. -/
theorem monsterNortonLineOneThreeTransportWord_binary : ∀ i : Fin 24,
    toAdd (monsterNortonLineOneThreeTransportImage monsterNortonLineOneThreeFourPointQ).base i =
      toAdd sourceOmegaQ.base i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
