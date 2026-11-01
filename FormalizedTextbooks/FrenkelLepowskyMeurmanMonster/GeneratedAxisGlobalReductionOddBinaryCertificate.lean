/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddActions

/-! Exact binding of all candidate binary columns to the original fourteen spatial actions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The candidate column bits, interpreted in the actual hyperbolic coordinate convention. -/
def generatedAxisGlobalOddCachedMatrix (k : Fin 14) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  fun i j => if (generatedAxisGlobalOddBinaryColumns k j).testBit i.val then 1 else 0

set_option maxHeartbeats 20000000 in
-- Verify all 8064 entries of the original sign and source-word binary actions.
/-- Every candidate bit is equal to the genuine lattice-induced binary action. -/
theorem generatedAxisGlobalOddCachedMatrix_certificate : ∀ k : Fin 14,
    generatedAxisGlobalOddCachedMatrix k = generatedAxisGlobalOddBinaryMatrix k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
