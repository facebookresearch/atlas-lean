/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddFastAction
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFastParity
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddForestStep

/-! Fast finite evaluation with exactly the existing genuine descending-edge meaning. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Cached arithmetic evaluation of the existing actual singular descending-edge obligation. -/
def generatedAxisGlobalOddFastStep (edge b : ℕ) : Prop :=
  generatedAxisGlobalFastSingular b = true →
    (edge = 31 ∧ b ∈ generatedAxisGlobalOddForestRootMasks) ∨
    (edge < 14 ∧ generatedAxisGlobalOddForestRank
      (generatedAxisGlobalOddFastInverse ⟨edge % 14, Nat.mod_lt _ (by decide)⟩ b) <
        generatedAxisGlobalOddForestRank b)

/-- The cache has precisely the original genuine edge meaning on every actual finite mask. -/
theorem generatedAxisGlobalOddFastStep_iff (edge b : ℕ) (hb : b < 2 ^ 24) :
    generatedAxisGlobalOddFastStep edge b ↔ generatedAxisGlobalOddForestStep edge b := by
  unfold generatedAxisGlobalOddFastStep generatedAxisGlobalOddForestStep
  rw [generatedAxisGlobalFastSingular_eq, generatedAxisGlobalOddFastInverse_eq _ _ hb]

/-- A checked cached edge proves the unchanged actual inverse-generator descending-edge theorem. -/
theorem generatedAxisGlobalOddFastStep_sound (edge b : ℕ) (hb : b < 2 ^ 24)
    (h : generatedAxisGlobalOddFastStep edge b) : generatedAxisGlobalOddForestStep edge b :=
  (generatedAxisGlobalOddFastStep_iff edge b hb).mp h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
