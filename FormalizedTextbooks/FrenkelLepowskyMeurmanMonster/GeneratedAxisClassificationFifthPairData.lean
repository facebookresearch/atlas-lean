/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthNumerator

/-! Finite pair-column witnesses excluding all actual pair lines from the inverse octad plane. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every actual pair has an inverse coordinate outside the original octad which is nonzero. -/
theorem generatedFifth_pair_outside_certificate : ∀ s : Fin 2, ∀ a b : Fin 24,
    a < b → ∃ i : Fin 24, Nat.testBit 0xcccc00 i.val = false ∧
      generatedFifthInverseNumerator i a * 4 +
        generatedFifthInverseNumerator i b * (if s = 0 then -4 else 4) ≠ 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
