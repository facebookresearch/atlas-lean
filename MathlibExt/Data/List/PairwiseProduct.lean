/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: replaced the unfolded lexicographic relation with `Prod.Lex`, moved the
theorem to the `List.Pairwise` namespace, narrowed imports, and added importing-client tests.
-/
module

public import Mathlib.Data.List.ProdSigma

/-! # Pairwise relations on list products

Adapted from `Coding.pairwise_product` in `eth/proof/networks/Coding/OccLists.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
The source spells out the lexicographic relation; this module uses the canonical `Prod.Lex`
relation and otherwise retains the source theorem's full generality.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace List

/-- The Cartesian product of two pairwise-related lists is pairwise-related in lexicographic
order. -/
theorem Pairwise.product_lex {α β : Type*} {r₁ : α → α → Prop} {r₂ : β → β → Prop}
    {l₁ : List α} {l₂ : List β} (h₁ : l₁.Pairwise r₁) (h₂ : l₂.Pairwise r₂) :
    (l₁ ×ˢ l₂).Pairwise (Prod.Lex r₁ r₂) := by
  induction l₁ with
  | nil => exact Pairwise.nil
  | cons x l ih =>
    rw [product_cons, pairwise_append]
    obtain ⟨hx, hl⟩ := pairwise_cons.1 h₁
    refine ⟨pairwise_map.2 (h₂.imp fun h => Prod.Lex.right x h), ih hl, ?_⟩
    intro p hp q hq
    obtain ⟨y, -, rfl⟩ := mem_map.1 hp
    obtain ⟨q₁, q₂⟩ := q
    exact Prod.Lex.left y q₂ (hx q₁ (mem_product.1 hq).1)

end List
