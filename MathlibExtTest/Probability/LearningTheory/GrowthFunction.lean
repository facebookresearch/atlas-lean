/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.GrowthFunction

@[expose] public section

/-- The empty class induces no labelings. -/
example : (restrictions (∅ : Finset (Fin 2 → Bool)) {0}).card ≤ 2 ^ 1 :=
  restrictions_card_le _ _

/-- The empty class does not shatter a nonempty sample. -/
example : ¬ Shatters (∅ : Finset (Fin 2 → Bool)) {0} := by
  rw [shatters_iff_card]
  simp [restrictions]

end
