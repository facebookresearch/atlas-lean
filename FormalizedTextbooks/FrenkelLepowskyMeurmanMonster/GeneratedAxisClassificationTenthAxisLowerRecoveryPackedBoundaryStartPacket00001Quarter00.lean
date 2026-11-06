/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryPacketGeneric

/-! Exact complete Start partition with symbolic elimination of literal zero coefficients. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Sixteen full original prefixes retain the entire twenty-four-entry physical numerator row.
/-- Complete weighted pre and stage-zero equations on one exact original sixteen-prefix block. -/
theorem generatedTenth_packed_boundary_start_0_00_01_quarter_0 :
    ∀ u : Fin 16,
      (∑ k : Fin 24, generatedTenthTwoFixerTensorNumerator 0 0 k *
        generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryPreWord 0 k
          (generatedTenthPackedBoundaryPacketPrefix 1 ⟨16 * 0 + u.val, by omega⟩))) =
        (generatedTenthTwoFixerTensorDenominator 0 : ℤ) *
          generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryStageWord 0 0 0
            (generatedTenthPackedBoundaryPacketPrefix 1 ⟨16 * 0 + u.val, by omega⟩)) := by
  have hrow : generatedTenthTwoFixerTensorNumerator 0 0 =
      ![-1, 0, 0, -1, -1, 0, 2, 1, -1, 0, 2, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by
    rfl
  simp only [hrow, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    zero_mul, zero_add]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
