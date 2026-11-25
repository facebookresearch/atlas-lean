/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.AutomorphismGroupPrimePowerKourovka18Problem82
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Cyclic groups at the prime-power divisibility threshold -/

open MathlibExt.GroupTheory.AutomorphismGroupPrimePowerKourovka18Problem82Wanted

-- One exponent works for all cyclic prime-power groups. The group of order two forces
-- that exponent to be at least two when the desired divisor is the prime itself.
example : ∃ k : ℕ, 2 ≤ k ∧ ∀ p : ℕ, p.Prime →
    p ∣ Nat.card (MulAut (Multiplicative (ZMod (p ^ k)))) := by
  obtain ⟨f, hf⟩ := autOrderPrimePowerBound_holds
  refine ⟨f 1, ?_, ?_⟩
  · by_contra! h
    have hd : 2 ^ f 1 ∣ Nat.card (Multiplicative (ZMod 2)) := by
      simpa [Nat.card_eq_fintype_card] using pow_dvd_pow 2 (show f 1 ≤ 1 by omega)
    have ha := hf 1 2 Nat.prime_two (Multiplicative (ZMod 2)) hd
    rw [IsCyclic.card_mulAut] at ha
    simp [Nat.card_eq_fintype_card, Nat.totient_two] at ha
  · intro p hp
    have : NeZero (p ^ f 1) := ⟨pow_ne_zero _ hp.ne_zero⟩
    simpa using hf 1 p hp (Multiplicative (ZMod (p ^ f 1))) (by simp [Nat.card_eq_fintype_card])
