/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.SAT.DPLL.Correctness
public import CSLibExt.Computability.CookLevin

@[expose] public section

/-!
# Client tests for deterministic DPLL

Smoke tests for CNF restriction, executable semantic reflection, deterministic
selection, and satisfiable and unsatisfiable DPLL examples.
-/

set_option autoImplicit false

open Cslib.Logic.PL
open Cslib.Algorithms.SAT.DPLL

private def allFalse : Nat → Bool := fun _ => false

private def exampleFormula : CNF :=
  [[(0, true), (1, false)], [(0, false)], [(2, true)]]

example : CNF.restrict (0, true) exampleFormula = [[], [(2, true)]] := by
  rfl

example : CNF.restrict (0, false) exampleFormula =
    [[(1, false)], [(2, true)]] := by
  rfl

example : firstUnit exampleFormula = some (0, false) := by
  rfl

example : firstVariable exampleFormula = some 0 := by
  rfl

example : clauseSatisfied allFalse [(0, false), (1, true)] = true := by
  rfl

example : clauseSatisfied allFalse [(0, true), (1, true)] = false := by
  rfl

example : formulaSatisfied allFalse [[(0, false)], [(1, false), (2, true)]] = true := by
  rfl

example : formulaSatisfied allFalse [[(0, false)], [(1, true)]] = false := by
  rfl

example : CNFClause.Satisfies allFalse [(0, false), (1, true)] := by
  exact clauseSatisfied_eq_true_iff.mp (by rfl)

example : CNF.Satisfies allFalse [[(0, false)], [(1, false), (2, true)]] := by
  exact formulaSatisfied_eq_true_iff.mp (by rfl)

example : dpll [[(0, true), (1, true)], [(0, false), (1, true)]] = true := by
  rfl

example : dpll [[(0, true)], [(0, false)]] = false := by
  rfl

example : dpll ([] : CNF) = true := by
  rfl

example : dpll ([[]] : CNF) = false := by
  rfl

example : CNFSat [[(0, true), (1, true)], [(0, false), (1, true)]] := by
  exact dpll_eq_true_iff.mp (by rfl)

example : ¬CNFSat [[(0, true)], [(0, false)]] := by
  intro hsatisfiable
  have := dpll_eq_true_iff.mpr hsatisfiable
  contradiction

#print axioms Cslib.Logic.PL.CNF.satisfies_restrict_iff
#print axioms Cslib.Algorithms.SAT.DPLL.clauseSatisfied_eq_true_iff
#print axioms Cslib.Algorithms.SAT.DPLL.formulaSatisfied_eq_true_iff
#print axioms Cslib.Algorithms.SAT.DPLL.dpll_eq_true_iff
