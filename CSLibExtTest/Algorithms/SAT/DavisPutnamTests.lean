/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.SAT.DavisPutnam.Basic
public meta import CSLibExt.Algorithms.SAT.DavisPutnam.Basic
public import CSLibExt.Algorithms.SAT.DPLL.Correctness
public meta import CSLibExt.Algorithms.SAT.DPLL.Correctness

@[expose] public section

/-!
# Tests for Davis-Putnam variable elimination

Single elimination steps (resolvents, dropped tautologies, untouched clauses), the full
procedure against the verified DPLL solver on satisfiable and unsatisfiable formulas
(including the pigeonhole formula for three pigeons and two holes), and the correctness
theorems applied to concrete formulas.
-/

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.SAT.DavisPutnam

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Algorithms.SAT.DPLL

-- `(x₀ ∨ x₁) ∧ (¬x₀ ∨ x₁)`: eliminating `x₀` leaves the resolvent `x₁ ∨ x₁`.
#guard eliminate 0 [[(0, true), (1, true)], [(0, false), (1, true)]] == [[(1, true), (1, true)]]
-- a tautological clause is dropped, a clause without `x₀` is kept
#guard eliminate 0 [[(0, true), (0, false)], [(2, false)]] == [[(2, false)]]
-- no negative occurrence: the positive clauses disappear
#guard eliminate 0 [[(0, true), (1, true)], [(1, false)]] == [[(1, false)]]
-- `x₀ ∧ ¬x₀` eliminates to the empty clause
#guard eliminate 0 [[(0, true)], [(0, false)]] == [[]]

/-- `n` clauses `x₀ ∨ xᵢ` with no negative occurrence of `x₀`. -/
private def posOnly (n : Nat) : CNF := (List.range n).map fun i ↦ [(0, true), (i + 1, true)]

-- Scale guard: the negative clauses are collected once, not once per positive clause.
#guard (eliminate 0 (posOnly 20000)).length == 0

/-- All four clauses over `x₀, x₁`: unsatisfiable. -/
private def allFour : CNF :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)],
    [(0, false), (1, false)]]

/-- Three pigeons in two holes: variable `2 * p + h` says pigeon `p` sits in hole `h`. -/
private def php32 : CNF :=
  [[(0, true), (1, true)], [(2, true), (3, true)], [(4, true), (5, true)],
    [(0, false), (2, false)], [(0, false), (4, false)], [(2, false), (4, false)],
    [(1, false), (3, false)], [(1, false), (5, false)], [(3, false), (5, false)]]

#guard davisPutnam [] == true
#guard davisPutnam [[]] == false
#guard davisPutnam allFour == false
#guard davisPutnam allFour.tail == true
#guard davisPutnam php32 == false
#guard davisPutnam php32.tail == true
#guard davisPutnam allFour == dpll allFour && davisPutnam php32 == dpll php32 &&
  davisPutnam php32.tail == dpll php32.tail

/-- The correctness theorem turns the computed answer into a proof of unsatisfiability. -/
example : ¬ CNFSat php32 := fun h ↦ by
  have := (davisPutnam_eq_true_iff php32).mpr h
  revert this
  decide

example : 3 ∉ (eliminate 3 php32).vars := not_mem_vars_eliminate 3 php32

end CSLibExtTest.Algorithms.SAT.DavisPutnam
