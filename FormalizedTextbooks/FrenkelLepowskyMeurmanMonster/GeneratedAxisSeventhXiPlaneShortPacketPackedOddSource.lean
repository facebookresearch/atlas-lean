/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPackedEvaluation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalCoordinates

/-! The whole original outgoing odd support and signs are bound to the finite packet catalogue. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The exact original source scalar multiplying the frame vector in an outgoing odd row. -/
def generatedSeventhXiShortOddScalar (d : Fin 2048) : ℤ :=
  -generatedSeventhXiTensorKappa d *
    (generatedSeventhXiTensorSpin ⟨d.val, by omega⟩ +
      generatedSeventhXiTensorSpin ⟨d.val + 2048, by omega⟩)

/-- The scalar retains the whole original canonical odd coefficient and denominator. -/
theorem generatedSeventhXiShortOddScalar_actual (d : Fin 2048) (j : Fin 24) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1
      (Sum.inr (Sum.inr (d, j))) =
      (generatedSeventhXiShortOddScalar d : ℝ) * (generatedSeventhXiTensorFrame j : ℝ) / 32 := by
  rw [generatedSeventhXi_canonical_axis_odd]
  simp only [generatedSeventhXiShortOddScalar, Int.cast_mul, Int.cast_neg, Int.cast_add,
    generatedSeventhXiTensorPacked_kappa, generatedSeventhXiTensorPacked_spin,
    generatedSeventhXiTensorPacked_frame, nortonUIntegerSign_real]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Every original low code, including every zero coefficient, is checked.
/-- The finite catalogue retains all original nonzero outgoing odd rows and their signed scalars. -/
theorem generatedSeventhXiShortPackedOdd_support : ∀ d : Fin 2048,
    if h : generatedSeventhXiShortPackedOddInverse d < 512 then
      let g : Fin 512 := ⟨generatedSeventhXiShortPackedOddInverse d, h⟩
      generatedSeventhXiShortPackedOddCode g = d ∧
        generatedSeventhXiShortOddScalar d =
          (if generatedSeventhXiShortPackedOddSignBits.testBit g.val then -1 else 1)
    else generatedSeventhXiShortOddScalar d = 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Every occupied original code occurs exactly once in the inverse catalogue.
/-- The original odd catalogue has its checked left inverse, without assuming injectivity. -/
theorem generatedSeventhXiShortPackedOdd_inverse : ∀ g : Fin 512,
    generatedSeventhXiShortPackedOddInverse (generatedSeventhXiShortPackedOddCode g) = g.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Bind every original theta and every physical code bit, including all source conventions.
/-- Packed odd theta and code masks are exactly their original source values. -/
theorem generatedSeventhXiShortPackedOdd_data : ∀ g : Fin 512,
    generatedSeventhXiShortPackedOddTheta g =
      generatedSeventhXiShortThetaSplit ⟨(generatedSeventhXiShortPackedOddCode g).val, by omega⟩ ∧
    generatedSeventhXiShortPackedOddMask g =
      generatedSeventhXiTensorMask (generatedSeventhXiShortPackedOddCode g) ∧
    golayBooleanCast (generatedSeventhXiShortPackedOddWeightBits.testBit g.val) =
      (if golayMaskWeight
          (generatedSeventhXiTensorMask (generatedSeventhXiShortPackedOddCode g)) % 8 = 0
        then (0 : ZMod 2) else 1) := by
  decide +kernel

/-- Checked inverse indices imply genuine injectivity of the occurring odd code catalogue. -/
theorem generatedSeventhXiShortPackedOddCode_injective :
    Function.Injective generatedSeventhXiShortPackedOddCode := by
  intro g h he
  apply Fin.ext
  rw [← generatedSeventhXiShortPackedOdd_inverse g,
    ← generatedSeventhXiShortPackedOdd_inverse h, he]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
