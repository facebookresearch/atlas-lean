/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorInputData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic

/-! Every complete integer output coordinate of the genuine candidate triality formula. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- The exact incoming odd coefficient uses the complete original source short dictionary. -/
def generatedTwelfthCandidateIncomingOddCoefficient (d : Fin 2048) (i : Fin 24) : ℤ :=
  generatedTwelfthIncomingShortCoefficient (Sum.inr (Sum.inr (d, i)))

/-- Every complete candidate incoming spin and spatial coordinate is retained in the output packet. -/
def generatedTwelfthCandidateIncomingTensorNumerator (n : Fin 4096) (i : Fin 24) : ℤ :=
  generatedTwelfthIncomingSpinTensorOutputInteger n i

/-- The complete original normalized XYZ numerator at any spin label and spatial column. -/
def generatedTwelfthCandidateFinalTensorInteger (n : Fin 4096) (i : Fin 24) : ℤ :=
  let d : Fin 2048 := ⟨n.val % 2048, Nat.mod_lt _ (by decide)⟩
  let sigma : ℤ := if (golayEncodedMask d.val).testBit i.val then -1 else 1
  let parker := nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  (if n.val < 2048 then 8 else -8) * sigma * generatedTwelfthCandidateIncomingOddCoefficient d i +
    sigma * parker * (generatedTwelfthCandidateIncomingTensorNumerator ⟨d.val, by omega⟩ i -
      generatedTwelfthCandidateIncomingTensorNumerator ⟨d.val + 2048, by omega⟩ i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
