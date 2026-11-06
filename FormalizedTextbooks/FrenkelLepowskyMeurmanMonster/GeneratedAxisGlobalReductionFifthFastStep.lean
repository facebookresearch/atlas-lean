/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthFastAction
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFastParity
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthForestStep

/-! Fast finite evaluation with exactly the existing genuine descending-edge meaning. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Cached arithmetic evaluation of the existing actual singular descending-edge obligation. -/
def generatedAxisGlobalFifthFastStep (edge b : ℕ) : Prop :=
  generatedAxisGlobalFastSingular b = true →
    (edge = 31 ∧ b ∈ generatedAxisGlobalFifthForestRootMasks) ∨
    (edge < 19 ∧ generatedAxisGlobalFifthForestRank
      (generatedAxisGlobalFifthFastInverse ⟨edge % 19, Nat.mod_lt _ (by decide)⟩ b) <
        generatedAxisGlobalFifthForestRank b)

/-- The cache has precisely the original genuine edge meaning on every actual finite mask. -/
theorem generatedAxisGlobalFifthFastStep_iff (edge b : ℕ) (hb : b < 2 ^ 24) :
    generatedAxisGlobalFifthFastStep edge b ↔ generatedAxisGlobalFifthForestStep edge b := by
  unfold generatedAxisGlobalFifthFastStep generatedAxisGlobalFifthForestStep
  rw [generatedAxisGlobalFastSingular_eq, generatedAxisGlobalFifthFastInverse_eq _ _ hb]

/-- A checked cached edge proves the unchanged actual inverse-generator descending-edge theorem. -/
theorem generatedAxisGlobalFifthFastStep_sound (edge b : ℕ) (hb : b < 2 ^ 24)
    (h : generatedAxisGlobalFifthFastStep edge b) : generatedAxisGlobalFifthForestStep edge b :=
  (generatedAxisGlobalFifthFastStep_iff edge b hb).mp h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
