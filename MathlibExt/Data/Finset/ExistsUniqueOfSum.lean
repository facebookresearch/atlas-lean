/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: moved the general finite-sum transport theorem into the `Finset`
namespace, renamed it for its composed summand, narrowed imports, and added client tests.
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card

/-! # Unique witnesses transported by universal finite-sum equality

If composition with a map preserves every integer-valued finite sum, then a property with a
unique witness in the target finset has a unique witness in the source finset.

Adapted from `eth/proof/networks/Value/Words.lean`, lines 51--67, in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace Finset

/-- If every integer-valued sum over `T` pulls back to the corresponding sum over `s`, then a
property with a unique witness in `T` pulls back to a property with a unique witness in `s`. -/
theorem existsUnique_of_sum_comp {α β : Type*} (s : Finset α) (T : Finset β) (i : α → β)
    (hsum : ∀ F : β → ℤ, ∑ a ∈ s, F (i a) = ∑ b ∈ T, F b)
    (Q : β → Prop) (hQ : ∃! b, b ∈ T ∧ Q b) : ∃! a, a ∈ s ∧ Q (i a) := by
  classical
  have h := hsum fun b => if Q b then 1 else 0
  simp only [Finset.sum_boole] at h
  obtain ⟨b, hb, hb'⟩ := hQ
  have hT : T.filter Q = {b} := by
    ext b'
    rw [mem_filter, mem_singleton]
    exact ⟨fun h' => hb' b' h', fun h' => h' ▸ hb⟩
  rw [hT, card_singleton] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1
    (by exact_mod_cast h : #(s.filter fun a => Q (i a)) = 1)
  have hm : ∀ a', a' ∈ s ∧ Q (i a') ↔ a' = a := fun a' => by
    have h' := @mem_filter _ (fun a => Q (i a)) _ s a'
    rw [ha, mem_singleton] at h'
    exact h'.symm
  exact ⟨a, (hm a).2 rfl, fun a' ha' => (hm a').1 ha'⟩

end Finset
