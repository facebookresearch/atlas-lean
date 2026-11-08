/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.MatroidGreedy
public meta import CSLibExt.Algorithms.Lean.Greedy.MatroidGreedy
public meta import Mathlib.Data.Finset.Sort

/-!
# Matroid greedy tests

The test matroid is the uniform matroid `U₂` on `ℕ` (a finite set is independent when it has at
most two elements), built with Mathlib's `IndepMatroid.ofFinset`. Executed fixtures check the
kept set and the cost on sorted inputs, including ties and inputs shorter than the rank. The
optimality and base theorems are instantiated on it.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

/-- The uniform matroid of rank two on `ℕ`. -/
private def uniform2 : Matroid ℕ :=
  (IndepMatroid.ofFinset Set.univ (fun I : Finset ℕ => I.card ≤ 2) (by simp)
    (fun _ _ hJ hIJ => (Finset.card_le_card hIJ).trans hJ)
    (fun I J hI hJ hlt => by
      obtain ⟨e, heJ, heI⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      exact ⟨e, heJ, heI, by rw [Finset.card_insert_of_notMem heI]; omega⟩)
    (fun _ _ => Set.subset_univ _)).matroid

private def oracle2 (S : Finset ℕ) : Bool := decide (S.card ≤ 2)

private theorem oracle2_spec : ∀ S, oracle2 S = true ↔ uniform2.Indep ↑S := by
  intro S
  simp only [oracle2, decide_eq_true_eq, uniform2, IndepMatroid.matroid_Indep]
  exact (IndepMatroid.ofFinset_indep (α := ℕ) Set.univ (fun I : Finset ℕ => I.card ≤ 2)
    _ _ _ _ (I := S)).symm

private meta def check (indep : Finset ℕ → Bool) (label : String) (es : List ℕ)
    (expected : List ℕ) (cost : ℕ) : IO Unit := do
  let r := matroidGreedy indep es
  let got := r.ret.sort (· ≤ ·)
  unless got == expected && r.time == cost do
    throw (IO.userError s!"{label}: got {got} with cost {r.time}")
  IO.println s!"{label}: {got}, cost {r.time}"

-- Weights equal the element's value, so each `es` is nonincreasing.
#eval check oracle2 "two heaviest of five" [9, 7, 4, 3, 1] [7, 9] 5
#eval check oracle2 "shorter than the rank" [5] [5] 1
#eval check oracle2 "empty" [] [] 0
#eval check oracle2 "duplicates are kept once" [8, 8, 2] [2, 8] 3

private def wt : ℕ → ℕ := id

example : ∑ x ∈ ({4, 3} : Finset ℕ), wt x ≤
    ∑ x ∈ (matroidGreedy oracle2 [9, 7, 4, 3, 1]).ret, wt x :=
  matroidGreedy_optimal oracle2_spec wt (by decide) ((oracle2_spec _).1 (by decide)) (by decide)

example : (matroidGreedy oracle2 [9, 7, 4, 3, 1]).ret = {9, 7} := by decide

example (es : List ℕ) : (matroidGreedy oracle2 es).time = es.length := matroidGreedy_time _ es

universe u

/-- The API at an arbitrary universe. -/
example {α : Type u} [DecidableEq α] {M : Matroid α} {indep : Finset α → Bool}
    (hind : ∀ S, indep S = true ↔ M.Indep ↑S) (w : α → ℕ) {es : List α}
    (hsorted : es.Pairwise fun a b => w b ≤ w a) {I : Finset α} (hI : M.Indep ↑I)
    (hIes : ∀ x ∈ I, x ∈ es) (hground : ∀ x, x ∈ M.E ↔ x ∈ es) :
    ∑ x ∈ I, w x ≤ ∑ x ∈ (matroidGreedy indep es).ret, w x ∧
      M.IsBase ↑(matroidGreedy indep es).ret :=
  ⟨matroidGreedy_optimal hind w hsorted hI hIes, matroidGreedy_isBase hind es hground⟩

/-- `U₂,₅`: the uniform matroid of rank two on the ground set `{0, …, 4}`. -/
private def uniform25 : Matroid ℕ :=
  (IndepMatroid.ofFinset ↑(Finset.range 5)
    (fun I : Finset ℕ => I ⊆ Finset.range 5 ∧ I.card ≤ 2) (by simp)
    (fun _ _ hJ hIJ => ⟨hIJ.trans hJ.1, (Finset.card_le_card hIJ).trans hJ.2⟩)
    (fun I J hI hJ hlt => by
      obtain ⟨e, heJ, heI⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      refine ⟨e, heJ, heI, Finset.insert_subset (hJ.1 heJ) hI.1, ?_⟩
      rw [Finset.card_insert_of_notMem heI]
      omega)
    (fun _ hI => Finset.coe_subset.2 hI.1)).matroid

private def oracle25 (S : Finset ℕ) : Bool := decide (S ⊆ Finset.range 5 ∧ S.card ≤ 2)

private theorem oracle25_spec : ∀ S, oracle25 S = true ↔ uniform25.Indep ↑S := by
  intro S
  simp only [oracle25, decide_eq_true_eq, uniform25, IndepMatroid.matroid_Indep]
  exact (IndepMatroid.ofFinset_indep (α := ℕ) ↑(Finset.range 5)
    (fun I : Finset ℕ => I ⊆ Finset.range 5 ∧ I.card ≤ 2) _ _ _ _ (I := S)).symm

/-- Listing the whole ground set heaviest first, greedy returns a base of `U₂,₅`. -/
example : uniform25.IsBase ↑(matroidGreedy oracle25 [4, 3, 2, 1, 0]).ret :=
  matroidGreedy_isBase oracle25_spec _ (fun x => by
    simp only [uniform25, IndepMatroid.matroid_E, IndepMatroid.ofFinset_E, Finset.coe_range,
      Set.mem_Iio, List.mem_cons, List.not_mem_nil, or_false]
    omega)

example : (matroidGreedy oracle25 [4, 3, 2, 1, 0]).ret = {4, 3} := by decide

#print axioms matroidGreedy
#print axioms matroidGreedy_indep
#print axioms matroidGreedy_isBase
#print axioms matroidGreedy_optimal
#print axioms matroidGreedy_time

end Cslib.Algorithms.Lean.TimeM
