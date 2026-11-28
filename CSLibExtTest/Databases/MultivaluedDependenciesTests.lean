/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.MultivaluedDependencies
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for multivalued and join dependencies

Attributes `A, B, C = 0, 1, 2`, values natural numbers.
* Boundary: in the course–teacher–book relation `ctb`, `A ↠ B` (and its complement `A ↠ C`)
  holds but `A → B` does not; the decomposition into `AB` and `AC` reconstructs `ctb`.
* Dropping two of its tuples breaks `A ↠ B`, and the decomposition becomes lossy.
* A relation satisfying `A → B` satisfies `A ↠ B` (rule FMVD1).
* Proposition 8.3.3 of Abiteboul–Hull–Vianu for `{A → B}`: `{AB, AC}` gives an implied
  multivalued dependency, `{AB, BC}` does not.
* A three-scheme join dependency that holds, and fails after removing one tuple.
* Fourth normal form is stronger than BCNF: with no functional dependencies and `A ↠ B`, the
  schema `ABC` is in BCNF but not in fourth normal form.
-/

@[expose] public section

namespace Cslib.Databases.MultivaluedDependenciesTests

open Cslib.Databases

/-- The tuple with values `a`, `b`, `c` on `A`, `B`, `C`. -/
def tup (a b c : ℕ) : Tuple (Fin 3) ℕ := ![some a, some b, some c]

/-- Course `A`, teacher `B`, book `C`: course 1 has teachers 1, 2 and books 1, 2, in every
combination. -/
def ctb : Finset (Tuple (Fin 3) ℕ) := {tup 1 1 1, tup 1 1 2, tup 1 2 1, tup 1 2 2}

theorem ctb_isOver : IsOver Finset.univ ctb := by
  unfold IsOver Tuple.IsOver
  decide

-- The boundary: `A ↠ B` holds in `ctb`, but `A → B` does not.
example : MVD.HoldsIn Finset.univ ⟨{0}, {1}⟩ ctb ∧
    ¬ FD.HoldsIn ⟨{0}, {1}⟩ (↑ctb : Set (Tuple (Fin 3) ℕ)) := by
  refine ⟨by decide, ?_⟩
  simp only [FD.HoldsIn, Finset.mem_coe]
  decide

-- Complementation: `A ↠ C` holds as well, directly and by `MVD.holdsIn_compl`.
example : MVD.HoldsIn Finset.univ ⟨{0}, {2}⟩ ctb := by decide

example : MVD.HoldsIn Finset.univ ⟨{0}, Finset.univ \ {1}⟩ ctb :=
  (MVD.holdsIn_compl (Finset.subset_univ _)).mp (by decide)

-- The exchange witness for `tup 1 1 1` and `tup 1 2 2` is `tup 1 1 2`.
example : ∃ w ∈ ctb, (∀ a ∈ ({0} ∪ {1} : Finset (Fin 3)), w a = tup 1 1 1 a) ∧
    ∀ a ∈ (Finset.univ \ {1} : Finset (Fin 3)), w a = tup 1 2 2 a :=
  (MVD.holdsIn_iff_exchange ctb_isOver (Finset.subset_univ _) (Finset.subset_univ _)).mp
    (by decide) _ (by decide) _ (by decide) (by decide)

-- `{AB, AC}` reconstructs `ctb`, through the binary criterion.
example : join (project {0, 1} ctb) (project {0, 2} ctb) = ctb :=
  join_project_eq_iff_mvd.mpr (by decide)

/-- Two of the four tuples of `ctb`. -/
def ctb₂ : Finset (Tuple (Fin 3) ℕ) := {tup 1 1 1, tup 1 2 2}

-- Without the other two tuples, `A ↠ B` fails and the decomposition is lossy.
example : ¬ MVD.HoldsIn Finset.univ ⟨{0}, {1}⟩ ctb₂ ∧
    join (project {0, 1} ctb₂) (project {0, 2} ctb₂) ≠ ctb₂ := by
  decide

/-- A relation over `ABC` satisfying `A → B`. -/
def s : Finset (Tuple (Fin 3) ℕ) := {tup 1 2 3, tup 1 2 4, tup 2 5 3}

theorem s_isOver : IsOver Finset.univ s := by
  unfold IsOver Tuple.IsOver
  decide

example : MVD.HoldsIn Finset.univ ⟨{0}, {1}⟩ s :=
  MVD.holdsIn_of_holdsIn_fd s_isOver (Finset.subset_univ _) (Finset.subset_univ _)
    (by simp only [FD.HoldsIn, Finset.mem_coe]; decide)

/-- `A → B`. -/
def FAB : Finset (FD (Fin 3)) := {⟨{0}, {1}⟩}

-- Proposition 8.3.3: `{A → B}` implies `A ↠ B` on `ABC` (`AB ∩ AC = A`) ...
example : ∀ r : Finset (Tuple (Fin 3) ℕ), IsOver ({0, 1} ∪ {0, 2}) r →
    SatisfiesOn FAB ({0, 1} ∪ {0, 2}) r →
      MVD.HoldsIn ({0, 1} ∪ {0, 2}) ⟨{0, 1} ∩ {0, 2}, {0, 1}⟩ r :=
  (mvd_implied_iff_derives (d₀ := 0) (d₁ := 1) (by decide) (by decide)).mpr (Or.inl (by decide))

-- ... but not `B ↠ A` (`AB ∩ BC = B`).
example : ¬ ∀ r : Finset (Tuple (Fin 3) ℕ), IsOver ({0, 1} ∪ {1, 2}) r →
    SatisfiesOn FAB ({0, 1} ∪ {1, 2}) r →
      MVD.HoldsIn ({0, 1} ∪ {1, 2}) ⟨{0, 1} ∩ {1, 2}, {0, 1}⟩ r := by
  intro h
  have := (mvd_implied_iff_derives (d₀ := 0) (d₁ := 1) (by decide) (by decide)).mp h
  revert this
  decide

/-- The join dependency `⋈[AB, BC, AC]`. -/
def jd3 : JD (Fin 3) := ⟨[{0, 1}, {1, 2}, {0, 2}]⟩

-- It holds in this relation, and fails once `tup 1 1 1` is removed, although that tuple is
-- still in the join of the projections.
example : jd3.HoldsIn ({tup 1 1 2, tup 1 2 1, tup 2 1 1, tup 1 1 1} : Finset (Tuple (Fin 3) ℕ)) ∧
    ¬ jd3.HoldsIn ({tup 1 1 2, tup 1 2 1, tup 2 1 1} : Finset (Tuple (Fin 3) ℕ)) := by
  decide

/-- `Studios` (Abiteboul–Hull–Vianu, Example 11.2.15): the single multivalued dependency
`A ↠ B` over `ABC`. -/
def Jstudio : Finset (JD (Fin 3)) := {MVD.toJD Finset.univ ⟨{0}, {1}⟩}

-- With no functional dependencies, `ABC` is in BCNF but not in fourth normal form: `A ↠ B` is
-- nontrivial and implied, but `A → ABC` fails in `ctb`.
example : IsBCNF (∅ : Finset (FD (Fin 3))) Finset.univ ∧
    ¬ IsFourthNF ℕ Finset.univ ∅ Jstudio := by
  refine ⟨by decide, fun h => ?_⟩
  have hFD := h.2 {0} (Finset.subset_univ _) {1} (Finset.subset_univ _) (by decide) (by decide)
    (fun _ _ _ hJ => hJ _ (Finset.mem_singleton_self _)) ctb ctb_isOver
    (fun _ hf => absurd hf (Finset.notMem_empty _)) (by decide)
  revert hFD
  simp only [FD.HoldsIn, Finset.mem_coe]
  decide

end Cslib.Databases.MultivaluedDependenciesTests
