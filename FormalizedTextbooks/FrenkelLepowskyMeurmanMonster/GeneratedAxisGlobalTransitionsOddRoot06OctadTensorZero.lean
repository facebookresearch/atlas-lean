/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadOutside

/-! Exact original input symmetry proves every outgoing scaled tensor is zero. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Exact original low-high symmetry and zero original odd short inputs give zero outgoing scaled tensors. -/
theorem generatedAxisGlobalOddRoot06PositiveTensorQ_zero :
    (generatedAxisGlobalRationalTriality (generatedAxisGlobalOddSparseRootPacket 1)).2.2 = 0 := by
  funext t j
  simp only [generatedAxisGlobalRationalTriality, generatedAxisGlobalTrialityScaledTensorQ,
    generatedAxisGlobalOddSparseRootPacket]
  let d := generatedAxisGlobalSpinLabelLow (generatedAxisGlobalSpinLabel t)
  let z : ℚ := if (golayEncodedMask d.val).testBit j.val then -1 else 1
  change (generatedAxisGlobalIntSign (t 11) : ℚ) * z *
    generatedAxisGlobalOddSparseShortQ 1 (Sum.inr (Sum.inr (d, j))) +
    (generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ℚ) * z *
      ((generatedAxisGlobalOddRationalRootPacket 1).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) j -
        (generatedAxisGlobalOddRationalRootPacket 1).2.2
          (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) j) / 2 = 0
  rw [generatedAxisGlobalOddRoot06Initial_odd_zero]
  dsimp only [generatedAxisGlobalOddRationalRootPacket,
    generatedAxisGlobalOddRationalRootSpin, generatedAxisGlobalOddRationalRootSpatial,
    generatedAxisGlobalOddRationalRootDenominator]
  rw [generatedAxisGlobalSpinLabel_coeff, generatedAxisGlobalSpinLabel_coeff]
  change (generatedAxisGlobalIntSign (t 11) : ℚ) * z * 0 +
    (generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ℚ) * z *
      ((generatedAxisGlobalOddRoot06Spin08 ⟨d.val, by omega⟩ : ℚ) *
        (generatedAxisGlobalOddRoot06Spatial08 j : ℚ) / 2 -
        (generatedAxisGlobalOddRoot06Spin08 ⟨d.val + 2048, by omega⟩ : ℚ) *
          (generatedAxisGlobalOddRoot06Spatial08 j : ℚ) / 2) / 2 = 0
  rw [generatedAxisGlobalOddRoot06Spin_low_high]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
