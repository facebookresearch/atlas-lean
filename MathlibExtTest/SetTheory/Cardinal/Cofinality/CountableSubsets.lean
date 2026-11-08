/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import MathlibExt.SetTheory.Cardinal.Cofinality.CountableSubsets
public import Mathlib.Data.Set.Countable
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

open Set Order

namespace MathlibExtTest.SetTheory.Cardinal.Cofinality.CountableSubsets

open MetaMathlibExt

-- Logic 37: Countable subsets of $\alpha$

/-- **Faithfulness**: membership is literally countability. -/

theorem mem_countableSubsets.{u} {α : Type u} (x : Set α) :
    x ∈ CountableSubsets α ↔ x.Countable := Iff.rfl

/-- Closed under countable unions — what makes the closure clause of a `[α]^ω`-club
satisfiable rather than a demand for membership of an uncountable set. -/

theorem countableSubsets_iUnion.{u} {α : Type u} (f : ℕ → Set α)
    (hf : ∀ n, f n ∈ CountableSubsets α) : (⋃ n, f n) ∈ CountableSubsets α :=
  Set.countable_iUnion hf

/-- **Degenerate case.**  For countable `α` the notion collapses to everything; it has
content exactly when `α` is uncountable. -/

theorem countableSubsets_eq_univ_iff.{u} (α : Type u) :
    CountableSubsets α = Set.univ ↔ Countable α := by
  constructor
  · intro h
    have hmem : (Set.univ : Set α) ∈ CountableSubsets α := by rw [h]; trivial
    exact Set.countable_univ_iff.mp hmem
  · intro h
    haveI := h
    ext x
    simp only [CountableSubsets, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact Set.to_countable x

-- Logic 39: Club in $[X]^\omega$

theorem _root_.MetaMathlibExt.IsClubOmega.nonempty.{u} {α : Type u} {C : Set (Set α)} (hC : IsClubOmega C) :
    C.Nonempty :=
  (hC.cofinal ∅ Set.countable_empty).imp fun _ hy => hy.1

/-- **The clauses are consistent.**  `closed` asserts membership of `⋃ n, f n`, which
`mem_countable` then requires to be countable — and it is.  So the two never conflict. -/

theorem IsClubOmega.iUnion_countable.{u} {α : Type u} {C : Set (Set α)} (hC : IsClubOmega C)
    (f : ℕ → Set α) (hf : ∀ n, f n ∈ C) : (⋃ n, f n).Countable :=
  Set.countable_iUnion fun n => hC.mem_countable _ (hf n)

/-- **Nontrivial**: `[α]^ω` is a club, so clubs always exist. -/

theorem isClubOmega_countableSubsets.{u} (α : Type u) : IsClubOmega (CountableSubsets α) where
  mem_countable := fun _ hx => hx
  cofinal := fun x hx => ⟨x, hx, subset_rfl⟩
  closed := fun _ hf _ => Set.countable_iUnion hf

/-- **Degenerate case**: `∅` is not a club — cofinality fails. -/

theorem not_isClubOmega_empty.{u} {α : Type u} : ¬ IsClubOmega (∅ : Set (Set α)) :=
  fun h => h.nonempty.ne_empty rfl

-- Logic 40: Stationarity in $[X]^\omega$

theorem not_isStationaryOmega_empty.{u} {α : Type u} :
    ¬ IsStationaryOmega (∅ : Set (Set α)) := by
  intro h
  obtain ⟨x, hx, -⟩ := h (isClubOmega_countableSubsets α)
  exact hx

/-- **Not vacuously false.**  `[α]^ω` is stationary, so the definition is satisfiable. -/

theorem isStationaryOmega_countableSubsets.{u} (α : Type u) :
    IsStationaryOmega (CountableSubsets α) :=
  fun _ hC => (hC.cofinal ∅ Set.countable_empty).imp
    fun y hy => ⟨hC.mem_countable y hy.1, hy.1⟩

-- Logic 41: Closure points

/-- No closure point is empty — `F ∅` would have to belong to it.  So `ClosurePoints F` never
contains the trivial witness, and the `cofinal` clause of a club built from it has real work
to do. -/

theorem notMem_closurePoints_empty {α : Type*} (F : Finset α → α) :
    (∅ : Set α) ∉ ClosurePoints F :=
  fun h => h.2 ∅ (by simp)

/-- Non-vacuity: for countable `α` the whole of `α` is a closure point of every `F`. -/

theorem univ_mem_closurePoints {α : Type*} (hα : (Set.univ : Set α).Countable)
    (F : Finset α → α) : (Set.univ : Set α) ∈ ClosurePoints F :=
  ⟨hα, fun _ _ => Set.mem_univ _⟩

-- Logic 51: Closure Points Sequence

/-- No closure point is empty — `F 0 ∅` would have to belong to it. -/

theorem notMem_closurePointsSeq_empty {α : Type*} (F : ℕ → Finset α → α) :
    (∅ : Set α) ∉ ClosurePointsSeq F :=
  fun h => h.2 0 ∅ (by simp)

/-- Non-vacuity: for countable `α` the whole of `α` is a closure point of every family. -/

theorem univ_mem_closurePointsSeq {α : Type*} (hα : (Set.univ : Set α).Countable)
    (F : ℕ → Finset α → α) : (Set.univ : Set α) ∈ ClosurePointsSeq F :=
  ⟨hα, fun _ _ _ => Set.mem_univ _⟩

end MathlibExtTest.SetTheory.Cardinal.Cofinality.CountableSubsets

end
