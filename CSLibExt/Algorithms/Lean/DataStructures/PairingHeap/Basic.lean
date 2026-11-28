/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Shared induction principle for the pairing-heap passes

Two-step induction for lists: `P []`, `P [a]`, and `P hs → P (a :: b :: hs)`.
Used by the `pass1` / `mergePairs` / `Tpass1` recursions of the pairing-heap
variants, which consume two list elements at a time. (The list variant's
`pass2` folds with `merge`, so it needs only ordinary list induction.)

Ported from the Chapter 23 Lean conversion in
`converted_proofs/ch23/lean/Chapter23.lean`, itself a conversion of the
Isabelle/HOL sources: the AFP entries `Pairing_Heap`
(`Pairing_Heap_List1.thy`, `Pairing_Heap_List2.thy`,
`Pairing_Heap_Tree.thy`) and `Amortized_Complexity`
(`Pairing_Heap_List2_Analysis.thy`, `Pairing_Heap_Tree_Analysis2.thy`),
and Tobias Nipkow (ed.), *Functional Data Structures and Algorithms:
A Proof Assistant Approach*, Chapter 23 (Pairing Heaps, pp. 257–264).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace PairingHeap

variable {α : Type u}

/-- Two-step induction for lists: `P []`, `P [a]`, and `P hs → P (a :: b :: hs)`.
Used for `pass1`, `mergePairs`, and `Tpass1`, whose recursion consumes two
list elements at a time. Proved by induction on the list length. -/
theorem List_pair_ind {P : List α → Prop}
    (nil : P []) (single : ∀ a, P [a])
    (cons2 : ∀ (a b : α) (hs : List α), P hs → P (a :: b :: hs))
    (hs : List α) : P hs := by
  have key : ∀ n : ℕ, ∀ hs : List α, hs.length ≤ n → P hs := by
    intro n
    induction n with
    | zero =>
      intro hs hh
      have : hs = [] := by
        cases hs with
        | nil => rfl
        | cons _ _ => simp at hh
      rw [this]; exact nil
    | succ n ih =>
      intro hs hh
      cases hs with
      | nil => exact nil
      | cons a hs =>
        cases hs with
        | nil => exact single a
        | cons b hs =>
          apply cons2 a b hs
          apply ih
          simp at hh ⊢; omega
  exact key hs.length hs le_rfl

end PairingHeap

end Cslib.Algorithms.Lean
