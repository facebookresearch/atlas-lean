/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMatrixData

/-! Exact integer square trace of the original signed pair-block matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

set_option maxHeartbeats 4000000 in
-- Sum all 576 original integer products in the complete matrix-square trace.
/-- The complete original denominator-cleared square trace is exactly 2816. -/
theorem generatedNinth_matrix_numerator_square_trace :
    (∑ i : Fin 24, ∑ j : Fin 24,
      generatedNinthMatrixNumerator i j * generatedNinthMatrixNumerator j i) = 2816 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
