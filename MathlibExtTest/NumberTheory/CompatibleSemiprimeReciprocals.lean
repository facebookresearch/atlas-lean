/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CompatibleSemiprimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-! # Regression tests for compatible semiprime reciprocals -/

namespace MetaMathlibExt

private noncomputable def compatibleReciprocal (n : ℕ) : ℝ :=
  Set.indicator {m : ℕ | ∃ p q r s, IsCompatibleSemiprimePair p q r s ∧ m = p * q}
    (fun m => (1 : ℝ) / m) n

-- A pair in Bradshaw's table contributes its reciprocal, not zero.
example : compatibleReciprocal (71 * 1609) = (1 : ℝ) / ((71 * 1609 : ℕ) : ℝ) := by
  have hm : 71 * 1609 ∈
      {m : ℕ | ∃ p q r s, IsCompatibleSemiprimePair p q r s ∧ m = p * q} :=
    ⟨71, 1609, 349, 491, isCompatibleSemiprimePair_71_1609, rfl⟩
  unfold compatibleReciprocal
  exact Set.indicator_of_mem hm _

-- A number outside the support makes no contribution.
example : compatibleReciprocal 1 = 0 := by
  have hm : 1 ∉ {m : ℕ | ∃ p q r s, IsCompatibleSemiprimePair p q r s ∧ m = p * q} := by
    rintro ⟨p, q, r, s, h, hpq⟩
    have hp := h.1.two_le
    have hq := h.2.1.two_le
    have hmul := Nat.mul_le_mul hp hq
    change 1 = p * q at hpq
    omega
  unfold compatibleReciprocal
  exact Set.indicator_of_notMem hm _

-- The theorem also bounds any injectively reindexed subseries.
example : Summable (fun n : ℕ => compatibleReciprocal (2 * n + 1)) := by
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b h
    change 2 * a + 1 = 2 * b + 1 at h
    omega
  exact summable_inv_compatibleSemiprimes.comp_injective hinj

end MetaMathlibExt
