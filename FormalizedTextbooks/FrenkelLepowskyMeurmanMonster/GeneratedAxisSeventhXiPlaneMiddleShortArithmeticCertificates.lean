/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleShortPairQ

/-! Actual integer-vector and central-phase checks use no opaque catalogue enumeration. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators

private def pairCode (p : Fin 276) : ℕ :=
  (generatedSeventhXiShortInputCoordinates p).1.val * 24 +
    (generatedSeventhXiShortInputCoordinates p).2.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Increasing neighboring codes avoid a quadratic comparison of the complete pair table.
private theorem input_pair_certificate :
    (∀ p : Fin 276, (generatedSeventhXiShortInputCoordinates p).1 <
      (generatedSeventhXiShortInputCoordinates p).2) ∧
    (∀ p : Fin 275, pairCode p.castSucc < pairCode p.succ) := by
  constructor
  · intro p
    fin_cases p <;> decide +kernel
  · intro p
    fin_cases p <;> decide +kernel

/-- The input coordinate data enumerate 276 distinct increasing pairs. -/
theorem generatedSeventhXiShort_input_pairs :
    (∀ p : Fin 276, (generatedSeventhXiShortInputCoordinates p).1 <
      (generatedSeventhXiShortInputCoordinates p).2) ∧
    (∀ p q : Fin 276, generatedSeventhXiShortInputCoordinates p =
      generatedSeventhXiShortInputCoordinates q → p = q) := by
  refine ⟨input_pair_certificate.1, ?_⟩
  have hm : StrictMono pairCode := Fin.strictMono_iff_lt_succ.mpr input_pair_certificate.2
  intro p q h
  apply hm.injective
  change (generatedSeventhXiShortInputCoordinates p).1.val * 24 +
      (generatedSeventhXiShortInputCoordinates p).2.val =
    (generatedSeventhXiShortInputCoordinates q).1.val * 24 +
      (generatedSeventhXiShortInputCoordinates q).2.val
  rw [h]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Finite descriptors retain their genuine pair, octad-code, or odd-vector bounds.
/-- Every output descriptor has the required genuine short-vector shape and unit physical sign. -/
theorem generatedSeventhXiShort_shapes : ∀ s : Fin 2, ∀ p : Fin 276,
    let d := generatedSeventhXiShortDescriptor s p
    (generatedSeventhXiShortPhysicalSign s p = 1 ∨
      generatedSeventhXiShortPhysicalSign s p = -1) ∧
    d 0 ≤ 2 ∧
    (if d 0 = 0 then d 1 < 2 ∧ d 2 < d 3 ∧ d 3 < 24
    else if d 0 = 1 then d 1 < 4096 ∧ golayMaskWeight (golayEncodedMask (d 1)) = 8 ∧
      d 2 < 64 ∧
      (∀ k l : Fin 8, k < l → generatedSeventhXiShortOctadCoordinates s p k <
        generatedSeventhXiShortOctadCoordinates s p l) ∧
      (∀ i : Fin 24, (golayEncodedMask (d 1)).testBit i.val = true ↔
        ∃ k : Fin 8, generatedSeventhXiShortOctadCoordinates s p k = i)
    else d 1 < 2048 ∧ d 2 < 24) := by
  intro s p
  fin_cases s <;> fin_cases p <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Each block checks the actual seventh matrix image and its full preferred-Q phase.
/-- Every original pair vector has its exact physical image and original central phase. -/
theorem generatedSeventhXiShort_arithmetic : ∀ s : Fin 2, ∀ b : Fin 18, ∀ i : Fin 16,
    if h : 16 * b.val + i.val < 276 then
      let p : Fin 276 := ⟨16 * b.val + i.val, h⟩
      (∀ j : Fin 24,
        8 * generatedSeventhXiShortPhysicalSign s p * generatedSeventhXiShortOutputIntegral s p j =
          ∑ k : Fin 24, generatedSeventhFrameVectorData 7 k j *
            generatedSeventhXiShortInputIntegral s p k) ∧
      toAdd (generatedSeventhXiMiddleQHom
        (generatedSeventhXiShortInputQ s p)).coeff =
          (generatedSeventhXiShortPhaseBit s p : ZMod 2)
    else True := by
  intro s b
  fin_cases s <;> fin_cases b <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
