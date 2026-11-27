/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Greedy.MatroidIntersection.Termination
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Combinatorics.Matroid.Constructions
import Mathlib.Tactic.FinCases

/-!
# Matroid intersection regression examples

Edges `0, 1, 2` have respectively (row, column) coordinates `(1,0), (0,0), (0,1)`.
The common set `{1}` cannot grow by a single insertion: the row source is `0`, the column
sink is `2`, and both exchanges in `0 → 1 → 2` are necessary.
-/

namespace Matroid.Intersection.Tests

open Set Relation
open scoped symmDiff

private abbrev E := Fin 3
private abbrev rows := (freeOn (univ : Set Bool)).comap (fun e : E ↦ decide (e = 0))
private abbrev cols := (freeOn (univ : Set Bool)).comap (fun e : E ↦ decide (e = 2))
private abbrev free := freeOn (univ : Set E)

-- Reduce these concrete partition matroids to injectivity of the row or column label.
local macro "fixture" : tactic => `(tactic|
  (simp only [Arc, Exchange, addable, mem_ofPred_eq, rows, cols, free, comap_indep_iff,
    freeOn_indep_iff, subset_univ, true_and, and_true, InjOn, mem_symmDiff] <;> decide))

private theorem sources (x : E) : x ∈ addable rows {1} ↔ x = 0 := by revert x; fixture
private theorem sinks (x : E) : x ∈ addable cols {1} ↔ x = 2 := by revert x; fixture

private def path : ℕ → E | 0 => 0 | 1 => 1 | _ => 2

private theorem three : Shortest rows cols {1} 2 path := by
  refine ⟨⟨(sources _).2 rfl, ?_, (sinks _).2 rfl⟩, ?_⟩
  · intro i hi
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · right; fixture
    · left; fixture
  · intro m q h
    have hs := (sources _).1 h.1
    have ht := (sinks _).1 h.2.2
    by_contra! hm
    obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    · exact (by decide : (0 : E) ≠ 2) (hs.symm.trans ht)
    · have e := h.2.1 0 (by decide)
      rw [hs, ht] at e
      exact (by fixture : ¬ Arc rows cols {1} 0 2) e

private theorem visited : vertices 2 path = univ := by
  apply eq_univ_of_forall
  intro x
  fin_cases x
  · exact ⟨0, Nat.zero_le _, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩

private theorem toggled : ({1} : Set E) ∆ vertices 2 path = {0, 2} := by
  rw [visited]
  ext x
  revert x
  simp only [mem_symmDiff, mem_univ, true_and, not_true_eq_false, and_false, false_or]
  decide

example : rows.Indep ({0, 2} : Set E) ∧ cols.Indep ({0, 2} : Set E) ∧
    ({0, 2} : Set E).ncard = ({1} : Set E).ncard + 1 :=
  toggled ▸ three.augment (by fixture) (by fixture)

-- First add the central edge by a one-vertex path, then take the two-arc path.
example : ReflTransGen (Step rows cols) ∅ ({0, 2} : Set E) := by
  have first : Shortest rows cols ∅ 0 (fun _ ↦ 1) :=
    ⟨⟨by fixture, fun _ hi ↦ by omega, by fixture⟩, fun _ _ _ ↦ Nat.zero_le _⟩
  have one : Step rows cols ∅ {1} := by
    refine ⟨_, _, first, ?_⟩
    ext x
    simp [vertices, mem_symmDiff]
  exact (ReflTransGen.single one).tail ⟨_, _, three, toggled.symm⟩

-- In the row/free intersection the maximal set {0,1} has no row source. The cut is
-- neither empty nor full: 2 is the sink, 1 reaches 2, and 0 cannot reach either.
private abbrev kept : Set E := {0, 1}

private theorem stopped : Terminal rows free kept := by
  rintro ⟨n, p, hs, _⟩
  have noSource : ∀ x : E, x ∉ addable rows kept := by fixture
  exact noSource _ hs

private theorem cut : canReachSink rows free kept = {1, 2} := by
  ext x
  constructor
  · rintro ⟨z, hz, h⟩
    have sink : ∀ v : E, v ∈ addable free kept → v ∈ ({1, 2} : Set E) := by fixture
    have pred : ∀ u v : E, Arc rows free kept u v →
        v ∈ ({1, 2} : Set E) → u ∈ ({1, 2} : Set E) := by fixture
    induction h using ReflTransGen.head_induction_on with
    | refl => exact sink z hz
    | head e _ ih => exact pred _ _ e ih
  · rintro (rfl | h)
    · exact ⟨2, by fixture, .single (Or.inl (by fixture))⟩
    · obtain rfl : x = 2 := h
      exact ⟨2, by fixture, .refl⟩

example : rows.eRk ({1, 2} : Set E) = 1 ∧ free.eRk ({1, 2} : Set E)ᶜ = 1 := by
  obtain ⟨h₁, h₂, -, -⟩ := stopped.certificate (by fixture) (by fixture) (by rfl) rfl
  rw [cut] at h₁ h₂
  have hi : kept ∩ {1, 2} = {1} := by ext x; revert x; decide
  have hd : kept \ {1, 2} = {0} := by ext x; revert x; decide
  simpa [hi, hd] using And.intro h₁ h₂

-- Internal chords alone do not suffice: 1 and 2 have the same row, and with I={0}
-- they are both sources and sinks. The walk 1 → 0 → 2 has no forward chord.
private def trap : ℕ → E | 0 => 1 | 1 => 0 | _ => 2

example : Joins rows free {0} 2 trap ∧ ¬ Arc rows free {0} 1 2 ∧
    ¬ Shortest rows free {0} 2 trap ∧ ¬ rows.Indep (({0} : Set E) ∆ vertices 2 trap) := by
  refine ⟨⟨by fixture, ?_, by fixture⟩, by fixture, ?_, ?_⟩
  · intro i hi
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · right; fixture
    · left; fixture
  · intro h
    have := h.2 0 (fun _ ↦ 2) ⟨by fixture, fun _ hi ↦ by omega, by fixture⟩
    omega
  · have hv : vertices 2 trap = univ := by
      apply eq_univ_of_forall
      intro x
      fin_cases x
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
    rw [hv]
    fixture

end Matroid.Intersection.Tests
