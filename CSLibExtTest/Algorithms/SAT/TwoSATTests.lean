/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.SAT.TwoSAT.Basic
public import CSLibExt.Algorithms.SAT.DPLL.Correctness
public meta import CSLibExt.Algorithms.SAT.TwoSAT.Basic
public meta import CSLibExt.Algorithms.SAT.DPLL.Solver

@[expose] public section

/-!
# Tests for 2-SAT through the implication graph

Runtime checks of the SCC-based procedure against the verified DPLL solver,
a proof-level use of the characterization, and a 3-CNF showing that the
2-CNF hypothesis is needed.
-/

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.SAT.TwoSAT

open Cslib.Logic.PL Cslib.Algorithms.SAT.TwoSAT Cslib.Algorithms.SAT.DPLL

/-- All four 2-clauses over `x₀, x₁`: unsatisfiable. -/
private def allFour : CNF :=
  [[(0, true), (1, true)], [(0, false), (1, true)], [(0, true), (1, false)],
    [(0, false), (1, false)]]

/-- Three of the four: satisfiable (`x₀ = x₁ = true`). -/
private def threeOfFour : CNF :=
  [[(0, true), (1, true)], [(0, false), (1, true)], [(0, true), (1, false)]]

/-- An implication chain `x₀ → x₁ → x₂ → ¬x₀` with `x₀` forced: unsatisfiable. -/
private def chain : CNF :=
  [[(0, false), (1, true)], [(1, false), (2, true)], [(2, false), (0, false)], [(0, true)]]

/-- The same chain without forcing `x₀`: satisfiable. -/
private def chainFree : CNF :=
  [[(0, false), (1, true)], [(1, false), (2, true)], [(2, false), (0, false)]]

#guard decide2SAT allFour = false
#guard decide2SAT threeOfFour = true
#guard decide2SAT chain = false
#guard decide2SAT chainFree = true
#guard decide2SAT [[(0, true)], [(0, false)]] = false
#guard decide2SAT [[(3, true), (3, true)]] = true
#guard decide2SAT ([] : CNF) = true
#guard decide2SAT [[]] = false

-- The SCC procedure agrees with DPLL on every example above.
#guard [allFour, threeOfFour, chain, chainFree, [[(0, true)], [(0, false)]], [], [[]]].all
  fun φ ↦ decide2SAT φ == dpll φ

example : IsTwoCNF allFour := by decide
example : IsTwoCNF chain := by decide

/-- Proof-level use of the characterization: `x₀ ∧ ¬x₀` is unsatisfiable because the unit
clauses give the edges `x₀ → ¬x₀` and `¬x₀ → x₀`. -/
example : ¬ CNFSat [[(0, true)], [(0, false)]] := by
  rw [cnfSat_iff_of_isTwoCNF (by decide)]
  rintro ⟨-, h⟩
  apply h 0
  constructor
  · exact Relation.ReflTransGen.single ⟨[(0, false)], by simp, by simp, by simp, by simp⟩
  · exact Relation.ReflTransGen.single ⟨[(0, true)], by simp, by simp, by simp, by simp⟩

/-- Edges respect skew symmetry. -/
example : ImpEdge chain (0, true) (1, true) := ⟨[(0, false), (1, true)], by simp [chain],
  by simp, by simp, by simp⟩

example : ImpEdge chain (1, false) (0, false) :=
  (show ImpEdge chain (0, true) (1, true) from
    ⟨[(0, false), (1, true)], by simp [chain], by simp, by simp, by simp⟩).skew

/-- The 2-CNF hypothesis is needed: on this satisfiable 3-CNF the clause-to-implication
reading is unsound and the procedure rejects. -/
private def threeCNF : CNF :=
  [[(0, true), (1, true), (2, true)], [(0, false), (1, false), (2, false)]]

#guard decide2SAT threeCNF = false
#guard dpll threeCNF = true
example : ¬ IsTwoCNF threeCNF := by decide

/-- A forced implication chain `x₀ → x₁ → ⋯ → x₂₉ → ¬x₀` with `x₀` asserted, over 60
literals: unsatisfiable. -/
private def longChain : CNF :=
  (List.range 29).map (fun i ↦ [(i, false), (i + 1, true)]) ++
    [[(29, false), (0, false)], [(0, true)]]

-- Scale regression: the successor lists are looked up in the precomputed table. Recomputing
-- them by scanning all literals and clauses on every DFS step made this input impractical.
#guard decide2SAT longChain = false
#guard decide2SAT longChain.dropLast = true

end CSLibExtTest.Algorithms.SAT.TwoSAT
