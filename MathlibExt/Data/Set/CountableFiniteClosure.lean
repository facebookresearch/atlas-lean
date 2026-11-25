/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Data.Set.Countable

/-!
# Countable closure under finite sets of successors

Starting with countably many generators, iteration of a finite successor
operation gives a countable set containing the generators and all successors.
No countability assertion is made about the algebraic span of this set.
-/

@[expose] public section
noncomputable section

namespace Set

universe u
variable {α : Type u}

/-- The finite-successor operation is applied once at each natural stage. -/
def finiteClosureStage (next : α → Finset α) (s : Set α) : ℕ → Set α
  | 0 => s
  | n + 1 => finiteClosureStage next s n ∪ ⋃ x ∈ finiteClosureStage next s n, (next x : Set α)

/-- The countable iteration of the finite-successor operation. -/
def finiteClosure (next : α → Finset α) (s : Set α) : Set α :=
  ⋃ n, finiteClosureStage next s n

lemma subset_finiteClosure (next : α → Finset α) (s : Set α) :
    s ⊆ finiteClosure next s := by
  intro x hx
  exact mem_iUnion.mpr ⟨0, hx⟩

lemma finiteClosure_closed (next : α → Finset α) (s : Set α)
    {x : α} (hx : x ∈ finiteClosure next s) : (next x : Set α) ⊆ finiteClosure next s := by
  rcases mem_iUnion.mp hx with ⟨n, hn⟩
  intro y hy
  apply mem_iUnion.mpr
  refine ⟨n + 1, Or.inr ?_⟩
  exact mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hn, hy⟩⟩

lemma Countable.finiteClosureStage {s : Set α} (hs : s.Countable)
    (next : α → Finset α) (n : ℕ) : (finiteClosureStage next s n).Countable := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    exact ih.union ((ih.biUnion_iff).mpr (fun x _ => (next x).countable_toSet))

lemma Countable.finiteClosure {s : Set α} (hs : s.Countable) (next : α → Finset α) :
    (finiteClosure next s).Countable :=
  countable_iUnion (hs.finiteClosureStage next)

end Set
