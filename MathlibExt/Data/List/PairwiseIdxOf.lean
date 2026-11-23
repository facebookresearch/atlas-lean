/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: moved the theorem into the `List.Pairwise` namespace, narrowed imports,
and added importing-client tests.
-/
/-
Modified by Meta Platforms, Inc. and affiliates: generalized the carrier universe.
-/
module

public import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-! # Positions in a list ordered by a map

Adapted from `eth/proof/networks/Coding/OccLists.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace List.Pairwise

/-- In a list along which `f` increases, position order agrees with value order. -/
theorem idxOf_lt_iff {α : Type*} [BEq α] [LawfulBEq α] {f : α → ℕ} {l : List α}
    (hl : l.Pairwise fun x y => f x < f y) {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    l.idxOf x < l.idxOf y ↔ f x < f y := by
  have key : ∀ {x y : α}, x ∈ l → y ∈ l → l.idxOf x < l.idxOf y → f x < f y := by
    intro x y hx hy h
    have hx' := List.idxOf_lt_length_of_mem hx
    have hy' := List.idxOf_lt_length_of_mem hy
    have h2 := List.pairwise_iff_getElem.1 hl _ _ hx' hy' h
    rwa [List.getElem_idxOf hx', List.getElem_idxOf hy'] at h2
  refine ⟨key hx hy, fun h => ?_⟩
  by_contra hn
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hn) with h' | h'
  · have := key hy hx h'
    omega
  · have e : y = x := (List.idxOf_inj hy).1 h'
    subst e
    omega

end List.Pairwise
