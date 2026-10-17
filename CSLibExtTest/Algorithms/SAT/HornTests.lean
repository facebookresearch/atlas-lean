/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.SAT.Horn.Basic
public import CSLibExt.Algorithms.SAT.DPLL.Correctness
public meta import CSLibExt.Algorithms.SAT.Horn.Basic
public meta import CSLibExt.Algorithms.SAT.DPLL.Solver

@[expose] public section

/-!
# Tests for Horn satisfiability

Least models computed by forward chaining, runtime agreement of `hornSat`
with the verified DPLL solver, proof-level uses of the least-model theorems,
and a non-Horn formula showing that the Horn hypothesis is needed.
(`close` is defined by well-founded recursion, so concrete runs use `#guard`.)
-/

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.SAT.Horn

open Cslib.Logic.PL Cslib.Algorithms.SAT.Horn Cslib.Algorithms.SAT.DPLL

/-- Facts `x₀`, rules `x₀ → x₁`, `x₁ ∧ x₀ → x₂`, and the goal clause `¬x₃`. -/
private def program : CNF :=
  [[(0, true)], [(0, false), (1, true)], [(1, false), (0, false), (2, true)], [(3, false)]]

/-- The same program with the goal clause `¬x₂`, contradicting the derivation of `x₂`. -/
private def refuted : CNF :=
  [[(0, true)], [(0, false), (1, true)], [(1, false), (0, false), (2, true)], [(2, false)]]

#guard close program ∅ = {0, 1, 2}
#guard hornSat program = true
#guard close refuted ∅ = {0, 1, 2}
#guard hornSat refuted = false
#guard hornSat ([] : CNF) = true
#guard hornSat [[]] = false
#guard hornSat [[(5, false), (6, false)]] = true
#guard close [[(5, false), (6, true)]] ∅ = ∅

-- `hornSat` agrees with DPLL on every Horn example above.
#guard [program, refuted, [], [[]], [[(5, false), (6, false)]], [[(5, false), (6, true)]]].all
  fun φ ↦ hornSat φ == dpll φ

example : IsHorn program := by decide
example : IsHorn refuted := by decide

/-- Least-model minimality, used at the proof level: every model of `program` makes `x₂`
true, because `x₂` is in the least model. -/
example (σ : Nat → Bool) (hσ : program.Satisfies σ) (h : leastModel program 2 = true) :
    σ 2 = true :=
  leastModel_le (by decide) hσ h

/-- Correctness, used at the proof level: a satisfying assignment certifies `hornSat`. -/
example : hornSat [[(0, true)], [(0, false), (1, true)]] = true :=
  (hornSat_eq_true_iff (by decide)).mpr
    (cnfSat_iff_exists_satisfies.mpr ⟨fun _ ↦ true, formulaSatisfied_eq_true_iff.mp (by rfl)⟩)

/-- The Horn hypothesis is needed: `(x₀ ∨ x₁) ∧ ¬x₀` is satisfiable but not Horn, and
forward chaining makes both `x₀` and `x₁` true, so `hornSat` rejects it. -/
private def nonHorn : CNF := [[(0, true), (1, true)], [(0, false)]]

#guard hornSat nonHorn = false
#guard dpll nonHorn = true
example : ¬ IsHorn nonHorn := by decide

end CSLibExtTest.Algorithms.SAT.Horn
