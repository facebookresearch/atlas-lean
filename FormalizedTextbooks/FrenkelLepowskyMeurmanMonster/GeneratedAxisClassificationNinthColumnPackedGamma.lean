/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedSoundness

/-! A periodic decoder for the already certified original diagonal Gaussian sign. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Sixteen-bit periodic sign with the original third-quarter sign reversal. -/
def generatedNinthColumnGammaPacked (n : Fin 4096) : ℤ :=
  if (0x7ee8 : ℕ).testBit (n.val % 16) != (n.val / 1024 == 2) then 1 else -1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Compare every periodic coordinate with the original frozen sign decoder.
/-- The periodic sign is exactly the original Gaussian sign at every spin label. -/
theorem generatedNinth_column_gamma_packed : ∀ n : Fin 4096,
    generatedNinthColumnGammaPacked n = generatedSixthSpinGammaFast n := by
  decide +kernel

/-- The original 64-term numerator with the equivalent periodic diagonal decoder. -/
def generatedNinthColumnXiPacked (v : NortonUIntegerVector) (n : Fin 4096) : ℤ :=
  ∑ a : Fin 64,
    let m := generatedSixthSpinLabelXor n (generatedSixthGrayCodeLabel a)
    let z := v m
    if z = 0 then 0 else generatedSixthGraySign a * generatedNinthColumnGammaPacked m * z

/-- Replacing the sign decoder preserves the entire original Gaussian operator. -/
theorem generatedNinth_column_xi_packed (v : NortonUIntegerVector) :
    generatedNinthColumnXiPacked v = generatedSixthIntegerXiCached v := by
  funext n
  unfold generatedNinthColumnXiPacked generatedSixthIntegerXiCached
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  rw [generatedNinth_column_gamma_packed]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
