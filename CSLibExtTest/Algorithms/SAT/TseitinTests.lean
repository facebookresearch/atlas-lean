/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.SAT.Tseitin.Basic
public import CSLibExt.Algorithms.SAT.DPLL.Correctness
public meta import CSLibExt.Algorithms.SAT.Tseitin.Basic

@[expose] public section

/-!
# Tests for the Tseitin transformation

The exact clauses produced for small formulas, the size bounds, and
equisatisfiability checked twice: through the correctness theorem and
independently by running the verified DPLL solver on the produced CNF.
-/

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.SAT.Tseitin

open Cslib.Logic Cslib.Logic.PL Proposition Cslib.Algorithms.SAT.DPLL

/-- Two ordinary atoms plus a separate falsum atom `⊥`. -/
inductive At where
  | falsum
  | x
  | y
  deriving DecidableEq

instance : Bot At := ⟨.falsum⟩

/-- Variable numbering of the atoms. -/
def ι : At → ℕ
  | .falsum => 0
  | .x => 1
  | .y => 2

theorem ι_injective : Function.Injective ι := by
  intro a b h
  cases a <;> cases b <;> simp_all [ι]

private def p : Proposition At := .atom .x
private def q : Proposition At := .atom .y

/-- `p ∧ q`: atoms become variables `2` and `4`, the gate is variable `1`. -/
example : tseitin ι (p ∧ q : Proposition At) =
    [[(1, true)], [(1, false), (2, true)], [(1, false), (4, true)],
      [(1, true), (2, false), (4, false)]] := by rfl

/-- Gates are numbered in post-order: in `(p ∨ q) → p` the disjunction is gate `0`
(variable `1`) and the implication gate `1` (variable `3`). -/
example : (tseitinAux ι ((p ∨ q) → p : Proposition At) 0).1 = (3, true) := by rfl

example : (tseitin ι (((p → q) → p) → p : Proposition At)).length = 3 * 3 + 1 := by rfl
example : (((p → q) → p) → p : Proposition At).connectiveCount = 3 := by rfl

example : ∀ C ∈ tseitin ι (((p → q) → p) → p : Proposition At), C.length ≤ 3 :=
  fun _ hC ↦ length_le_three_of_mem_tseitin ι _ hC

/-- The CNF of a contradiction is unsatisfiable, by the theorem. -/
example : ¬ CNFSat (tseitinBot ι (p ∧ ¬p : Proposition At)) := by
  rw [cnfSat_tseitinBot_iff ι_injective]
  rintro ⟨v, hv, h⟩
  rw [evalBool_and, evalBool_neg hv] at h
  cases hx : v .x <;> simp_all [p]

/-- The same, independently, by running the verified DPLL solver on the produced CNF. -/
example : dpll (tseitinBot ι (p ∧ ¬p : Proposition At)) = false := by decide

/-- The negation of Peirce's law is unsatisfiable (checked by DPLL), and Peirce's law
itself is satisfiable. -/
example : dpll (tseitinBot ι (¬(((p → q) → p) → p) : Proposition At)) = false := by decide
example : dpll (tseitinBot ι (((p → q) → p) → p : Proposition At)) = true := by decide

/-- A satisfiable formula: the theorem and DPLL agree. -/
example : CNFSat (tseitinBot ι (p ∨ q : Proposition At)) :=
  (cnfSat_tseitinBot_iff ι_injective _).mpr ⟨fun a ↦ decide (a = .x), rfl, by decide⟩

example : dpll (tseitinBot ι (p ∨ q : Proposition At)) = true := by decide

/-- Without the unit clause for `⊥`, the atom `⊥` is an ordinary variable: `tseitin` of
`⊥` alone is satisfiable. -/
example : CNFSat (tseitin ι (⊥ : Proposition At)) := by
  exact cnfSat_iff_exists_satisfies.mpr ⟨fun _ ↦ true, formulaSatisfied_eq_true_iff.mp (by rfl)⟩

example : ¬ CNFSat (tseitinBot ι (⊥ : Proposition At)) := by
  rw [cnfSat_tseitinBot_iff ι_injective]
  rintro ⟨v, hv, h⟩
  simp [hv] at h

/-- A left-nested conjunction with `n` connectives. -/
private def leftNest : ℕ → Proposition At
  | 0 => p
  | n + 1 => (leftNest n ∧ q : Proposition At)

-- Regression for the builder: each operand is encoded once and each gate prepends its three
-- clauses to an accumulator. Recomputing the left operand made depth 60 take about 2^60
-- steps; concatenating the operands' clause lists made depth 2000 quadratic.
#guard (tseitin ι (leftNest 60)).length = 3 * 60 + 1
#guard (tseitin ι (leftNest 2000)).length = 3 * 2000 + 1

end CSLibExtTest.Algorithms.SAT.Tseitin
