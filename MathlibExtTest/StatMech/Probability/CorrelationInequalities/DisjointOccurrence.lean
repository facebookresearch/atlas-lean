/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.DisjointOccurrence

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.DisjointOccurrence`

The definition `disjointOccurrence` quantifies over coordinate sets `K L : Set E`, so it is not
decidable as stated; these tests compute it by hand on `ConfigSpace (Fin 2)`:
* `agreeOn` and `OccursOn` at small inputs (`OccursOn` of "coordinate `0` open" on `{0}` and its
  failure on `∅`);
* `open0 □ open0 = ∅`: an event cannot be witnessed twice on disjoint coordinate sets when it
  needs coordinate `0` both times;
* `open0 □ open1 = open0 ∩ open1 = {⊤}`: events about different coordinates occur disjointly
  exactly when both occur;
* `disjointOccurrence_subset_inter`, `disjointOccurrence_comm`, `disjointOccurrence_mono` applied
  to these events.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.DisjointOccurrence

open _root_.StatMech

/-- The event "coordinate `0` is open" on two coordinates. -/
def open0 : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

/-- The event "coordinate `1` is open" on two coordinates. -/
def open1 : Set (ConfigSpace (Fin 2)) := {ω | ω 1 = true}

-- `agreeOn` on the empty set holds for any two configurations.
example (ω ω' : ConfigSpace (Fin 2)) : agreeOn ∅ ω ω' := by
  intro e he
  exact absurd he (Set.notMem_empty e)

-- `agreeOn {0}` distinguishes configurations that differ at `0`.
example : ¬ agreeOn {0} (fun _ : Fin 2 => true) (fun _ => false) := by
  intro h
  simpa using h 0 rfl

-- `open0` occurs on `{0}` at the all-open configuration.
example : OccursOn open0 {0} (fun _ => true) := by
  intro ω' h
  simpa [open0] using h 0 rfl

-- `open0` does not occur on `∅`: the empty witness does not force coordinate `0` open.
example : ¬ OccursOn open0 ∅ (fun _ => true) := by
  intro h
  simpa [open0] using h (fun _ => false) (fun e he => absurd he (Set.notMem_empty e))

/-- If `open0` occurs on `K` at `ω`, then `0 ∈ K`. -/
theorem mem_of_occursOn_open0 {K : Set (Fin 2)} {ω : ConfigSpace (Fin 2)}
    (h : OccursOn open0 K ω) : (0 : Fin 2) ∈ K := by
  by_contra h0
  have hmem := h (Function.update ω 0 false) (fun e he => by
    have : e ≠ 0 := fun he0 => h0 (he0 ▸ he)
    simp [Function.update_of_ne this])
  simp [open0] at hmem

-- `open0 □ open0 = ∅`: both witnesses would contain coordinate `0`.
theorem disjointOccurrence_open0_self : disjointOccurrence open0 open0 = ∅ := by
  ext ω
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨K, L, hKL, hK, hL⟩
  exact Set.disjoint_left.mp hKL (mem_of_occursOn_open0 hK) (mem_of_occursOn_open0 hL)

-- The all-open configuration lies in `open0 □ open1`, witnessed by `K = {0}` and `L = {1}`.
example : (fun _ => true) ∈ disjointOccurrence open0 open1 := by
  refine ⟨{0}, {1}, by simp, ?_, ?_⟩
  · intro ω' h
    simpa [open0] using h 0 rfl
  · intro ω' h
    simpa [open1] using h 1 rfl

-- `open0 □ open1 = open0 ∩ open1`: the events concern different coordinates.
theorem disjointOccurrence_open0_open1 :
    disjointOccurrence open0 open1 = open0 ∩ open1 := by
  refine subset_antisymm (disjointOccurrence_subset_inter _ _) ?_
  rintro ω ⟨h0, h1⟩
  refine ⟨{0}, {1}, by simp, ?_, ?_⟩
  · intro ω' h
    exact (h 0 rfl).trans h0
  · intro ω' h
    exact (h 1 rfl).trans h1

-- Hence `open0 □ open1` is exactly the all-open configuration.
example : disjointOccurrence open0 open1 = {fun _ => true} := by
  rw [disjointOccurrence_open0_open1]
  ext ω
  simp only [open0, open1, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i <;> assumption
  · rintro rfl
    exact ⟨rfl, rfl⟩

-- `disjointOccurrence_comm` on the concrete events.
example : disjointOccurrence open1 open0 = open0 ∩ open1 := by
  rw [disjointOccurrence_comm, disjointOccurrence_open0_open1]

-- `disjointOccurrence_mono`: enlarging `open0` to `univ` keeps the all-open configuration.
example : (fun _ => true) ∈ disjointOccurrence Set.univ open1 :=
  disjointOccurrence_mono (Set.subset_univ open0) le_rfl
    (by rw [disjointOccurrence_open0_open1]; exact ⟨rfl, rfl⟩)

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.DisjointOccurrence
