/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingSourceData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnData

/-! Integer XYZ arithmetic retaining the original odd phase and both source spin rows. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original XYZ numerator in source labels, with denominator sixty-four times sqrt two. -/
def generatedNinthFinalColumnArithmetic (n : Fin 4096) : ℤ :=
  let d : Fin 2048 := ⟨n.val % 2048, Nat.mod_lt _ (by decide)⟩
  let sigma : ℤ := if (golayEncodedMask d.val).testBit 1 then -1 else 1
  let parker := nortonUIntegerSign
    (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  (if n.val < 2048 then 4 else -4) * sigma * generatedNinthIncomingCoefficient d +
    sigma * parker *
      (generatedNinthColumnSpinData 9 ⟨d.val, by omega⟩ -
        generatedNinthColumnSpinData 9 ⟨d.val + 2048, by omega⟩)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
