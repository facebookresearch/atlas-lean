/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite
import MathlibExt.GroupTheory.ResiduallyFiniteP

open MathlibExt.GroupTheory.KourovkaNotebookShared

-- The condition is vacuous in the trivial group.
example (p : ℕ) : IsResiduallyFiniteP p Unit :=
  fun g hg => absurd (Subsingleton.elim g 1) hg

-- A cyclic group of order 4 is residually a finite 2-group: the trivial subgroup has index 2 ^ 2.
example : IsResiduallyFiniteP 2 (Multiplicative (ZMod 4)) := by
  intro g hg
  refine ⟨⊥, Subgroup.normal_bot, ⟨2, ?_⟩, by simpa using hg⟩
  rw [Subgroup.index_bot, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rfl

-- The index must be a power of `p`: in a cyclic group of order 3 the only normal subgroup of
-- index a power of 2 is the whole group.
example : ¬ IsResiduallyFiniteP 2 (Multiplicative (ZMod 3)) := by
  intro h
  obtain ⟨N, -, ⟨k, hk⟩, hg⟩ := h (Multiplicative.ofAdd 1) (by decide)
  have hcard : Nat.card (Multiplicative (ZMod 3)) = 3 :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 3)
  have hdvd : 2 ^ k ∣ 3 := by
    rw [← hk]
    exact N.index_dvd_card.trans (dvd_of_eq hcard)
  have hk0 : k = 0 := by
    rcases k with _ | k
    · rfl
    · exact absurd ((dvd_pow_self 2 k.succ_ne_zero).trans hdvd) (by decide)
  rw [hk0, pow_zero, Subgroup.index_eq_one] at hk
  exact hg (hk ▸ Subgroup.mem_top _)
