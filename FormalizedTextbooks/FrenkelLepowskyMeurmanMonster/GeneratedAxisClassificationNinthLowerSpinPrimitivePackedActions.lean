/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitiveUnits
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedMetadata
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinQMaskGeneric

/-! Genuine full extraspecial primitive action, independent of full-word source certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The original twelve-coordinate Golay reader equals the exact finite mask decoder. -/
theorem generatedNinth_lower_spin_primitive_packed_label_decode (d : Fin 4096) :
    golayLabelCoefficients d = monsterCo1GeometryBinaryMaskDecode (n := 12) d.val := by
  funext j
  simp only [golayLabelCoefficients, monsterCo1GeometryBinaryMaskDecode]

/-- Every full label is its exact binary-mask lift with the original central coefficient. -/
theorem generatedNinth_lower_spin_primitive_packed_normal_form (w : ℕ) :
    generatedNinthLowerSpinPrimitivePackedQ w =
      qCentral (generatedNinthLowerSpinPrimitivePackedCentral w) *
        generatedAxisGlobalQMask (generatedNinthLowerSpinPrimitivePackedBinary w) := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    apply toAdd.injective
    simpa only [generatedNinthLowerSpinPrimitivePackedQ, generatedAxisGlobalQMask,
      generatedNinthLowerSpinPrimitivePackedBinary, toAdd_ofAdd,
      generatedNinth_lower_spin_primitive_packed_label_decode] using
      (generatedAxisGlobalSourceMaskJoin_decode (w % 4096) ((w / 4096) % 4096)).symm
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    change generatedNinthLowerSpinPrimitivePackedCentral w =
      generatedNinthLowerSpinPrimitivePackedCentral w + 0
    rw [add_zero]

/-- Genuine primitive local fibers preserve the original square form for both signs. -/
theorem generatedNinth_lower_spin_primitive_packed_square (l : GeneratedNinthLowerSpinLetter)
    (v : Fin 24 → ZMod 2) :
    squareQuad (qBinaryAction (spinConjugation (generatedNinthLowerSpinFiberLetter l).val.1) v) =
      squareQuad v := by
  change squareQuad (spinBinaryAction (generatedNinthLowerSpinFiberLetter l).val.1 v) = _
  rw [(generatedNinthLowerSpinFiberLetter l).property]
  exact leechBinaryAction_squareQuad _ v

/-- Complete binary masks and exact central cochains evaluate every genuine signed primitive. -/
theorem generatedNinth_lower_spin_primitive_packed_mask_actual
    (l : GeneratedNinthLowerSpinLetter) (v : ℕ) :
    spinConjugation (generatedNinthLowerSpinFiberLetter l).val.1 (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage
        (generatedNinthLowerSpinPrimitivePackedColumns
          (generatedNinthLowerSpinPrimitivePackedIndex l))
        (generatedNinthLowerSpinPrimitivePackedRows (generatedNinthLowerSpinPrimitivePackedIndex l))
        (generatedNinthLowerSpinPrimitivePackedCoefficients
          (generatedNinthLowerSpinPrimitivePackedIndex l)) v := by
  have hm := generatedNinth_lower_spin_primitive_packed_metadata
    (generatedNinthLowerSpinPrimitivePackedIndex l)
  unfold generatedNinthLowerSpinPrimitivePackedMetadata at hm
  rw [generatedNinth_lower_spin_primitive_packed_letter_index] at hm
  exact generatedNinth_lower_spin_q_mask_from_units _
    (generatedNinth_lower_spin_primitive_packed_square l)
    (generatedNinthLowerSpinPrimitiveQGenerator l) _ _ _
    (generatedNinth_lower_spin_primitive_units_generator l) hm.1 hm.2.1 hm.2.2 v

/-- Packed labels retain their actual original central coefficient under genuine conjugation. -/
theorem generatedNinth_lower_spin_primitive_packed_actual
    (l : GeneratedNinthLowerSpinLetter) (w : ℕ) :
    spinConjugation (generatedNinthLowerSpinFiberLetter l).val.1
        (generatedNinthLowerSpinPrimitivePackedQ w) =
      qCentral (generatedNinthLowerSpinPrimitivePackedCentral w) *
        generatedAxisGlobalQMaskImage
          (generatedNinthLowerSpinPrimitivePackedColumns
            (generatedNinthLowerSpinPrimitivePackedIndex l))
          (generatedNinthLowerSpinPrimitivePackedRows
            (generatedNinthLowerSpinPrimitivePackedIndex l))
          (generatedNinthLowerSpinPrimitivePackedCoefficients
            (generatedNinthLowerSpinPrimitivePackedIndex l))
          (generatedNinthLowerSpinPrimitivePackedBinary w) := by
  rw [generatedNinth_lower_spin_primitive_packed_normal_form, map_mul,
    spinConjugation_central, generatedNinth_lower_spin_primitive_packed_mask_actual]

/-- Finite packed vector and central identities prove the SAME original primitive Q evaluator. -/
theorem generatedNinth_lower_spin_primitive_evaluation_of_packed
    (l : GeneratedNinthLowerSpinLetter) (input output : ℕ)
    (h : generatedNinthLowerSpinPrimitivePackedCondition l input output) :
    generatedNinthLowerSpinPrimitiveQEvaluation l (generatedNinthLowerSpinPrimitivePackedQ input) =
      generatedNinthLowerSpinPrimitivePackedQ output := by
  rw [← generatedNinth_lower_spin_primitive_units_evaluation,
    generatedNinth_lower_spin_primitive_packed_actual]
  dsimp only [generatedNinthLowerSpinPrimitivePackedCondition] at h
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    apply toAdd.injective
    have hb := congrArg (monsterCo1GeometryBinaryMaskDecode (n := 24)) h.1
    simpa only [generatedAxisGlobalQMaskImage, generatedNinthLowerSpinPrimitivePackedQ,
      toAdd_ofAdd, generatedNinth_lower_spin_primitive_packed_label_decode] using
      hb.trans (generatedAxisGlobalSourceMaskJoin_decode
        (output % 4096) ((output / 4096) % 4096))
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    exact h.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
