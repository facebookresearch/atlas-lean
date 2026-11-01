/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineParameterMatrix
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The two translation readings followed by the twelve actual modulation coordinates. -/
def generatedAxisFourthQAffineParameterEncode (p : SpinIndex × SpinIndex) : Fin 14 → ZMod 2 :=
  Fin.append ![p.1 1, p.1 11] p.2

private theorem parameter_encode_decode (w : Fin 14 → ZMod 2) :
    generatedAxisFourthQAffineParameterEncode
      (generatedAxisFourthQAffineParameterDecode w) = w := by
  funext i
  induction i using Fin.addCases (m := 2) (n := 12) with
  | left i =>
    simp only [generatedAxisFourthQAffineParameterEncode, Fin.append_left]
    have h : golayLabelCoefficients 14 (1 : Fin 12) = 1 ∧
        golayLabelCoefficients 2048 (1 : Fin 12) = 0 ∧
        golayLabelCoefficients 14 (11 : Fin 12) = 0 ∧
        golayLabelCoefficients 2048 (11 : Fin 12) = 1 := by decide +kernel
    fin_cases i
    · change (w 0 • golayLabelCoefficients 14 + w 1 • golayLabelCoefficients 2048) 1 = w 0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h.1, h.2.1,
        mul_one, mul_zero, add_zero]
    · change (w 0 • golayLabelCoefficients 14 + w 1 • golayLabelCoefficients 2048) 11 = w 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h.2.2.1, h.2.2.2,
        mul_one, mul_zero, zero_add]
  | right i => exact Fin.append_right _ _ i

private theorem parameter_decode_encode (p : SpinIndex × SpinIndex)
    (hp : p.1 ∈ generatedAxisFourthQAffineParameterPlane) :
    generatedAxisFourthQAffineParameterDecode
      (generatedAxisFourthQAffineParameterEncode p) = p := by
  apply Prod.ext
  · exact (generatedAxisFourthQAffineParameter_plane_mem_iff p.1).mp hp |>.symm
  · funext i
    exact Fin.append_right _ _ i

/-- The actual affine family kernel is exactly the counted fourteen-parameter space. -/
def generatedAxisFourthQAffineParameterEquiv :
    generatedAxisFourthQAffineFamilyKernel generatedAxisFourthQAffineParameterPlane
      generatedAxisFourthQAffineParameterBases generatedAxisFourthQAffineParameterCharacters 0 ≃
        generatedFourthQParameterSpace where
  toFun p := ⟨generatedAxisFourthQAffineParameterEncode p.val, by
    apply (generatedAxisFourthQAffineParameter_decode_mem_iff _).mp
    rw [parameter_decode_encode p.val p.property.1]
    exact p.property⟩
  invFun w := ⟨generatedAxisFourthQAffineParameterDecode w.val,
    (generatedAxisFourthQAffineParameter_decode_mem_iff w.val).mpr w.property⟩
  left_inv p := by exact Subtype.ext (parameter_decode_encode p.val p.property.1)
  right_inv w := by exact Subtype.ext (parameter_encode_decode w.val)

/-- Exactly 128 actual translation-modulation pairs fix the declared twenty-two affine states. -/
theorem generatedAxisFourthQAffineParameter_kernel_card :
    Nat.card (generatedAxisFourthQAffineFamilyKernel generatedAxisFourthQAffineParameterPlane
      generatedAxisFourthQAffineParameterBases generatedAxisFourthQAffineParameterCharacters 0) =
        128 := by
  rw [Nat.card_congr generatedAxisFourthQAffineParameterEquiv,
    generatedFourthQParameterSpace_card]

/-- The actual common Q stabilizer of the declared affine spin family has exactly 128 elements.
Identification of this declared family with the fourth axis tensor is a separate theorem. -/
theorem generatedAxisFourthQAffineParameter_stabilizer_card :
    Nat.card (generatedAxisFourthQAffineFamilyStabilizer generatedAxisFourthQAffineParameterPlane
      generatedAxisFourthQAffineParameterBases generatedAxisFourthQAffineParameterCharacters) =
        128 := by
  rw [generatedAxisFourthQAffineFamily_card generatedAxisFourthQAffineParameterPlane
    generatedAxisFourthQAffineParameterBases generatedAxisFourthQAffineParameterCharacters 0,
    generatedAxisFourthQAffineParameter_kernel_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
