/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairCountData

/-! Summing the original Golay labels after the exact source-fiber convolution. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Both source parities contribute according to the actual encoded weight and support bits. -/
def leechNormSixPairLabelContribution (d : Fin 4096) : ℕ :=
  let w := golayMaskWeight (golayEncodedMask d.val)
  let a : ZMod 2 := ((golayEncodedMask d.val).testBit 0).toNat
  let b : ZMod 2 := ((golayEncodedMask d.val).testBit 1).toNat
  leechNormSixPairExpectedContribution false w a b +
    leechNormSixPairExpectedContribution true w a b

/-- Original encoder coordinates and the displayed natural support masks give identical fibers. -/
theorem leechNormSixPairExpectedContribution_label (m : Bool) (d : Fin 4096) :
    leechNormSixPairExpectedContribution m
      (∑ i, ((golayCodeLabelEquiv d).val i).val)
      ((golayCodeLabelEquiv d).val 0) ((golayCodeLabelEquiv d).val 1) =
    leechNormSixPairExpectedContribution m (golayMaskWeight (golayEncodedMask d.val))
      (((golayEncodedMask d.val).testBit 0).toNat : ZMod 2)
      (((golayEncodedMask d.val).testBit 1).toNat : ZMod 2) := by
  have hb (i : Fin 24) : golayEncoder (golayLabelCoefficients d) i =
      (((golayEncodedMask d.val).testBit i.val).toNat : ZMod 2) := by
    rw [← ZMod.natCast_zmod_val (golayEncoder (golayLabelCoefficients d) i),
      golayLabelEncoder_match]
    cases h : (golayEncodedMask d.val).testBit i.val <;> rfl
  simp only [golayCodeLabelEquiv_val]
  rw [← golayLabel_weight, hb 0, hb 1, Fin.val_zero, Fin.val_one]

set_option maxHeartbeats 8000000 in
-- Sum all 4,096 original Golay labels using the verified source-fiber contributions.
set_option maxRecDepth 100000 in
/-- The actual encoder outputs sum to 953856 paired source solutions. -/
theorem leechNormSixPairLabelContribution_sum :
    (∑ d : Fin 4096, leechNormSixPairLabelContribution d) = 953856 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
