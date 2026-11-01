/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorWeightParity0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorWeightParity1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorWeightParity2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorWeightParity3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorWeightParity4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorWeightParity5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorWeightParity6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorWeightParity7

/-! Original weight certificates simplify the tensor evaluator without changing its integer
value. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The cache is exactly one fourth of the genuine physical Golay code weight modulo two. -/
theorem generatedSixth_tensor_weight_parity (d : Fin 2048) :
    generatedSixthTensorWeightParity d =
      (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) := by
  have h : ∀ b : Fin 8, ∀ a : Fin 256,
      generatedSixthTensorWeightParity (Fin.ofNat 2048 (b.val * 256 + a.val)) =
        (golayMaskWeight (golayEncodedMask (b.val * 256 + a.val)) / 4 : ℕ) := by
    intro b a
    fin_cases b
    · exact generatedSixth_tensor_weight_parity0 a
    · exact generatedSixth_tensor_weight_parity1 a
    · exact generatedSixth_tensor_weight_parity2 a
    · exact generatedSixth_tensor_weight_parity3 a
    · exact generatedSixth_tensor_weight_parity4 a
    · exact generatedSixth_tensor_weight_parity5 a
    · exact generatedSixth_tensor_weight_parity6 a
    · exact generatedSixth_tensor_weight_parity7 a
  let b : Fin 8 := ⟨d.val / 256, by omega⟩
  let a : Fin 256 := ⟨d.val % 256, by omega⟩
  have he : b.val * 256 + a.val = d.val := by dsimp [b, a]; omega
  have hd : Fin.ofNat 2048 (b.val * 256 + a.val) = d := by
    apply Fin.ext
    simp only [Fin.val_ofNat, he]
    omega
  have hh := h b a
  rw [hd] at hh
  simpa only [he] using hh

/-- Exact original tensor evaluation with only the genuine code-weight sign cached. -/
def generatedSixthTensorFastExecutable (n : Fin 4096) (j : Fin 24) : ℤ :=
  let d := generatedSixthTensorDictionary n
  let s : ℤ := if (golayEncodedMask d.val).testBit j.val then -1 else 1
  8 * nortonUIntegerSign (if n.val.testBit 11 then 1 else 0) * s *
    generatedSixthMiddleOddPackedNumerator d j -
      nortonUIntegerSign (generatedSixthTensorWeightParity d) * s *
        generatedSixthFrameVectorData 8 0 j *
          (generatedSixthPackedSpinPhase ⟨d.val, by omega⟩ -
            generatedSixthPackedSpinPhase ⟨d.val + 2048, by omega⟩)

/-- The faster value equals the original full tensor numerator on every actual address. -/
theorem generatedSixth_tensor_fast_executable (n : Fin 4096) (j : Fin 24) :
    generatedSixthTensorFastExecutable n j = generatedSixthTensorExecutable n j := by
  simp only [generatedSixthTensorFastExecutable, generatedSixthTensorExecutable,
    generatedSixth_tensor_weight_parity]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
