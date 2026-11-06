/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFrameData

/-! Finite denominator-cleared diagonal data from the original nine-factor frame action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Thirty-two times each expected diagonal coordinate, before and after exterior triality. -/
def generatedNinthDiagonalNumerator : Fin 24 → ℤ :=
  ![10, 10, 10, 12, 10, 12, 10, 10, 12, 12, 10, 12,
    12, 10, 10, 10, 10, 10, 12, 10, 12, 10, 10, 10]

set_option maxRecDepth 20000 in
/-- The original fifth diagonal and the genuine inverse frame determine every cached entry. -/
theorem generatedNinth_diagonal_certificate : ∀ i : Fin 24,
    (∑ k : Fin 24, (if Nat.testBit 0x0f000f k.val then (2 : ℤ) else 1) *
      generatedNinthFrameVectorData 9 k i * generatedNinthFrameVectorData 9 k i) =
        8 * generatedNinthDiagonalNumerator i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
