/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthQCoordinateEvaluation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitMasks

/-! Packed columns evaluate the actual ninth binary action. Central phases are handled separately
by the exact source cochain; no signed action is inferred from a binary equation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Packed columns of the twenty-four checked original coordinate images. -/
def generatedNinthQBinaryColumns (i : Fin 24) : ℕ :=
  (generatedNinthCoordinateImageLabels i).1.val +
    4096 * (generatedNinthCoordinateImageLabels i).2.1.val

private theorem original_binary_product (l : List Q) :
    toAdd l.prod.base = (l.map (fun q => toAdd q.base)).sum := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    change toAdd q.base + toAdd l.prod.base =
      toAdd q.base + (l.map (fun r => toAdd r.base)).sum
    rw [ih]

set_option maxHeartbeats 4000000 in
-- Bind all576 bits of the stated columns to the actual original coordinate images.
/-- Every packed column has the actual checked binary coordinates, in the original orientation. -/
theorem generatedNinth_Q_binary_columns_actual (i j : Fin 24) :
    sixthFrameOrbitColumnMatrix generatedNinthQBinaryColumns i j =
      toAdd (generatedNinthCoordinateImage j).base i := by
  revert i j
  decide +kernel

/-- The genuine full evaluator induces exactly the stated packed-column matrix on the quotient. -/
theorem generatedNinth_Q_binary_coordinate_evaluation (q : Q) :
    toAdd (generatedNinthQCoordinateEvaluation q).base =
      sixthFrameOrbitColumnMatrix generatedNinthQBinaryColumns *ᵥ toAdd q.base := by
  unfold generatedNinthQCoordinateEvaluation monsterNortonCoordinateEvaluation
  rw [qCentral_mul_base]
  rw [original_binary_product, List.map_ofFn, List.sum_ofFn]
  ext i
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [generatedNinth_Q_binary_columns_actual]
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by
    intro z
    fin_cases z <;> simp
  change toAdd (if toAdd q.base j = 0 then (1 : Q)
    else generatedNinthCoordinateImage j).base i =
      toAdd (generatedNinthCoordinateImage j).base i * toAdd q.base j
  rcases hz (toAdd q.base j) with hj | hj
  · simp only [hj, ite_true, mul_zero]
    rfl
  · simp only [hj, one_ne_zero, ite_false, mul_one]

/-- Ordinary XOR column selection decodes to the actual binary image of every source lift. -/
theorem generatedNinth_Q_binary_mask_evaluation (n : ℕ) (q : Q)
    (hq : toAdd q.base = monsterCo1GeometryBinaryMaskDecode n) :
    toAdd (generatedNinthQCoordinateEvaluation q).base =
      monsterCo1GeometryBinaryMaskDecode
        (sixthFrameOrbitMaskApply generatedNinthQBinaryColumns n) := by
  rw [generatedNinth_Q_binary_coordinate_evaluation, hq,
    sixthFrameOrbitMaskApply_decode]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
