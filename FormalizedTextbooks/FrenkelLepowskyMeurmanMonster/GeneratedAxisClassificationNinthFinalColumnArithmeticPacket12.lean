/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmetic

/-! Exact original XYZ arithmetic on source-label block 12. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Check the original signed XYZ integer formula on exactly256 source labels.
/-- The original XYZ numerator equals the cached column on every label in this block. -/
theorem generatedNinth_final_column_arithmetic_packet_12 : ∀ m : Fin 256,
    generatedNinthFinalColumnArithmetic ⟨3072 + m.val, by omega⟩ =
      generatedNinthFinalColumnInteger ⟨3072 + m.val, by omega⟩ := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
