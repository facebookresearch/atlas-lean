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
# Countable closure under finite successor sets

Let next : α → Finset α assign a finite successor set to each element. Starting from s ⊆ α,
define s₀ = s and sₙ₊₁ = sₙ ∪ ⋃_{x∈sₙ} next(x). Their union over n : ℕ contains s and is
closed under next.

If s is countable, every stage sₙ is countable, since it adds a countable union of finite
sets. The union of all stages is therefore countable as well. The construction applies in any
universe for α.
-/

@[expose] public section
noncomputable section

namespace Set

universe u
variable {α : Type u}

/-- Stages of closure under finite successor sets.

For next : α → Finset α and s ⊆ α, define s₀ = s and sₙ₊₁ = sₙ ∪ ⋃_{x∈sₙ} next(x). Each stage
includes the preceding stage and all successors of its elements. -/
def finiteClosureStage (next : α → Finset α) (s : Set α) : ℕ → Set α
  | 0 => s
  | n + 1 => finiteClosureStage next s n ∪ ⋃ x ∈ finiteClosureStage next s n, (next x : Set α)

/-- Union of the finite-successor closure stages.

For next : α → Finset α and s ⊆ α, finiteClosure next s is ⋃_{n : ℕ} sₙ, where s₀ = s and sₙ₊₁
adds the successors of all elements of sₙ. -/
def finiteClosure (next : α → Finset α) (s : Set α) : Set α :=
  ⋃ n, finiteClosureStage next s n

/-- Inclusion of generators in their finite-successor closure.

For every successor operation next : α → Finset α and set s, the inclusion s ⊆ finiteClosure
next s holds because s is stage zero. -/
lemma subset_finiteClosure (next : α → Finset α) (s : Set α) :
    s ⊆ finiteClosure next s := by
  intro x hx
  exact mem_iUnion.mpr ⟨0, hx⟩

/-- Stability of the closure under finite successors.

If x belongs to finiteClosure next s, every element of next(x) also belongs to this closure.
If x occurs at stage n, its successors occur at stage n+1. -/
lemma finiteClosure_closed (next : α → Finset α) (s : Set α)
    {x : α} (hx : x ∈ finiteClosure next s) : (next x : Set α) ⊆ finiteClosure next s := by
  rcases mem_iUnion.mp hx with ⟨n, hn⟩
  intro y hy
  apply mem_iUnion.mpr
  refine ⟨n + 1, Or.inr ?_⟩
  exact mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hn, hy⟩⟩

/-- Countability of each finite-successor closure stage.

If s ⊆ α is countable and next assigns a finite set to every element, then finiteClosureStage
next s n is countable for every natural stage n. -/
lemma Countable.finiteClosureStage {s : Set α} (hs : s.Countable)
    (next : α → Finset α) (n : ℕ) : (finiteClosureStage next s n).Countable := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    exact ih.union ((ih.biUnion_iff).mpr (fun x _ => (next x).countable_toSet))

/-- Countability of the closure under finite successors.

For countable s ⊆ α and next : α → Finset α, the union finiteClosure next s is countable,
being the countable union of its countable natural-number stages. -/
lemma Countable.finiteClosure {s : Set α} (hs : s.Countable) (next : α → Finset α) :
    (finiteClosure next s).Countable :=
  countable_iUnion (hs.finiteClosureStage next)

end Set
