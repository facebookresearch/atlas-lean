/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQTranslation

/-! The genuine full Eighth axis has trivial Q stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Membership in the full-axis Q stabilizer is exactly being the identity element. -/
theorem generatedEighth_Q_stabilizer_mem_iff (q : Q) :
    q ∈ generatedEighthAxisQStabilizer ↔ q = 1 := by
  constructor
  · exact generatedEighth_Q_fixed_eq_one q
  · rintro rfl
    exact generatedEighthAxisQStabilizer.one_mem

/-- The actual Q stabilizer subgroup is the trivial subgroup. -/
theorem generatedEighth_Q_stabilizer_eq_bot : generatedEighthAxisQStabilizer = ⊥ := by
  ext q
  exact generatedEighth_Q_stabilizer_mem_iff q

/-- The actual Q stabilizer has cardinality one. -/
theorem generatedEighth_Q_stabilizer_card : Nat.card generatedEighthAxisQStabilizer = 1 := by
  rw [generatedEighth_Q_stabilizer_eq_bot]
  simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
