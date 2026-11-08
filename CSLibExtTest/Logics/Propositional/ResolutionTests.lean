/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.CNF.Resolution
public import CSLibExt.Algorithms.SAT.DPLL.Correctness

@[expose] public section

/-!
# Tests for resolution soundness and refutation completeness

Concrete resolvents, explicit refutations, a refutation obtained from the
completeness theorem with unsatisfiability certified by the verified DPLL
solver, and non-refutability of satisfiable formulas.
-/

set_option autoImplicit false

namespace CSLibExtTest.Logics.Propositional.Resolution

open Cslib.Logic.PL Cslib.Algorithms.SAT.DPLL

/-- Resolving `x₀ ∨ x₁` with `¬x₀ ∨ x₂` on `x₀`. -/
example : CNFClause.resolvent 0 [(0, true), (1, true)] [(0, false), (2, true)] =
    [(1, true), (2, true)] := by rfl

/-- Every occurrence of the resolved literals is removed. -/
example : CNFClause.resolvent 0 [(0, true), (1, true), (0, true)] [(0, false), (0, false)] =
    [(1, true)] := by rfl

/-- An explicit refutation of `x₀ ∧ ¬x₀`. -/
example : CNF.ResolutionDerivable [[(0, true)], [(0, false)]] [] :=
  .resolve (C := [(0, true)]) (D := [(0, false)]) 0 (.ax (by simp)) (.ax (by simp))
    (by simp) (by simp)

/-- A two-step refutation of `{x₀ ∨ x₁, ¬x₀ ∨ x₁, ¬x₁}`. -/
example : CNF.ResolutionDerivable [[(0, true), (1, true)], [(0, false), (1, true)], [(1, false)]]
    [] := by
  have h01 : CNF.ResolutionDerivable
      [[(0, true), (1, true)], [(0, false), (1, true)], [(1, false)]] [(1, true), (1, true)] :=
    .resolve (C := [(0, true), (1, true)]) (D := [(0, false), (1, true)]) 0
      (.ax (by simp)) (.ax (by simp)) (by simp) (by simp)
  exact .resolve (D := [(1, false)]) 1 h01 (.ax (by simp)) (by simp) (by simp)

/-- The four clauses over two variables, unsatisfiable by DPLL, have a refutation. -/
example : CNF.ResolutionDerivable
    [[(0, true), (1, true)], [(0, false), (1, true)], [(0, true), (1, false)],
      [(0, false), (1, false)]] [] := by
  apply CNF.resolutionDerivable_nil_of_not_cnfSat
  intro hsat
  have := dpll_eq_true_iff.mpr hsat
  revert this
  decide

/-- A formula containing the empty clause is refuted by the axiom rule. -/
example : CNF.ResolutionDerivable [[(3, true)], []] [] := .ax (by simp)

/-- Satisfiable formulas, including the empty formula, have no refutation. -/
example : ¬ CNF.ResolutionDerivable ([] : CNF) [] := fun h ↦
  CNF.not_cnfSat_of_resolutionDerivable_nil h ⟨fun _ ↦ false, by simp⟩

example : ¬ CNF.ResolutionDerivable [[(0, true), (1, true)], [(0, false), (1, true)]] [] :=
  fun h ↦ CNF.not_cnfSat_of_resolutionDerivable_nil h (dpll_eq_true_iff.mp (by rfl))

/-- Derived clauses are semantic consequences: from `x₀ ∨ x₁` and `¬x₀ ∨ x₁` every
satisfying assignment makes `x₁` true. -/
example (v : Nat → Bool)
    (hv : CNF.Satisfies v [[(0, true), (1, true)], [(0, false), (1, true)]]) :
    v 1 = true := by
  have h : CNF.ResolutionDerivable [[(0, true), (1, true)], [(0, false), (1, true)]]
      [(1, true), (1, true)] :=
    .resolve (C := [(0, true), (1, true)]) (D := [(0, false), (1, true)]) 0
      (.ax (by simp)) (.ax (by simp)) (by simp) (by simp)
  simpa using h.satisfies hv

end CSLibExtTest.Logics.Propositional.Resolution
