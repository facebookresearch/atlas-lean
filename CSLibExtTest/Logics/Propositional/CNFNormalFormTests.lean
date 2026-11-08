/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.CNF.NormalForm
public meta import CSLibExt.Logics.Propositional.CNF.NormalForm
public import CSLibExt.Algorithms.SAT.DPLL.Correctness

@[expose] public section

/-!
# Tests for equivalent conjunctive normal forms

Exact CNFs of small propositions, the exponential growth of distribution, the
equivalence theorem at concrete assignments, and classical satisfiability
checked by the verified DPLL solver.
-/

set_option autoImplicit false

namespace CSLibExtTest.Logics.Propositional.CNFNormalForm

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

example : toCNF ι (p ∧ q : Proposition At) = [[(1, true)], [(2, true)]] := by decide
example : toCNF ι (p ∨ q : Proposition At) = [[(1, true), (2, true)]] := by decide
example : toCNF ι (p → q : Proposition At) = [[(1, false), (2, true)]] := by decide
example : toNegCNF ι (p → q : Proposition At) = [[(1, true)], [(2, false)]] := by decide
/-- `¬p` is `p → ⊥`: one clause `¬x ∨ ⊥`. -/
example : toCNF ι (¬p : Proposition At) = [[(1, false), (0, true)]] := by decide

/-- Distribution: `(x ∧ y) ∨ (x ∧ y) ∨ (x ∧ y)` has `2 ^ 3` clauses. -/
example : (toCNF ι ((p ∧ q) ∨ (p ∧ q) ∨ (p ∧ q) : Proposition At)).length = 8 := by decide

/-- `x₀ ∨ x₁`, `x₂ ∨ x₃`, … conjoined: already in CNF, with an exponential complement. -/
private def conjOfOrs : Nat → Proposition Nat
  | 0 => .or (.atom 0) (.atom 1)
  | n + 1 => .and (conjOfOrs n) (.or (.atom (2 * n + 2)) (.atom (2 * n + 3)))

-- Scale guard: `toCNF` builds only the positive polarity, so 40 conjuncts give 40 clauses
-- without the `2 ^ 40`-clause complement.
#guard (toCNF id (conjOfOrs 39)).length == 40
#guard (toNegCNF id (conjOfOrs 3)).length == 16

/-- `((x₀ ∧ x₁) ∧ x₂) ∧ …`, nested to the left. -/
private def leftAnd : Nat → Proposition Nat
  | 0 => .atom 0
  | n + 1 => .and (leftAnd n) (.atom (n + 1))

/-- `((x₀ ∨ x₁) ∨ x₂) ∨ …`, nested to the left. -/
private def leftOr : Nat → Proposition Nat
  | 0 => .atom 0
  | n + 1 => .or (leftOr n) (.atom (n + 1))

/-- `x₀ ∨ (x₁ ∨ (x₂ ∨ …))`, nested to the right. -/
private def rightOr (k : Nat) : Nat → Proposition Nat
  | 0 => .atom k
  | n + 1 => .or (.atom k) (rightOr (k + 1) n)

-- Scale guards: deep chains on either side are linear (an accumulator for conjunctions,
-- left-to-right distribution for disjunction chains), not quadratic.
#guard (toCNF id (leftAnd 20000)).length == 20001
#guard (toCNF id (leftOr 20000)).map List.length == [20001]
#guard (toCNF id (rightOr 0 20000)).map List.length == [20001]
#guard (toNegCNF id (leftOr 20000)).length == 20001
#guard toCNF id (leftOr 2) == [[(0, true), (1, true), (2, true)]]
#guard toCNF id (rightOr 0 2) == [[(0, true), (1, true), (2, true)]]

/-- The equivalence theorem at a concrete assignment. -/
example : (toCNF ι (p → q : Proposition At)).Satisfies (fun _ ↦ false) :=
  (satisfies_toCNF_iff ι _ _).mpr (by simp [p, q])

example : ¬ (toCNF ι (p ∧ q : Proposition At)).Satisfies (fun n ↦ decide (n = 1)) := by
  rw [satisfies_toCNF_iff]
  simp [p, q, ι]

/-- Classical satisfiability: `x ∧ ¬x` with `¬⊥` added is unsatisfiable (theorem and DPLL),
while `x → y` is satisfiable. -/
example : ¬ CNFSat ([(ι ⊥, false)] :: toCNF ι (p ∧ ¬p : Proposition At)) := by
  rw [cnfSat_toCNF_bot_iff ι_injective]
  rintro ⟨v, hv, h⟩
  rw [evalBool_and, evalBool_neg hv] at h
  cases hx : v .x <;> simp_all [p]

example : dpll ([(ι ⊥, false)] :: toCNF ι (p ∧ ¬p : Proposition At)) = false := by decide
example : dpll ([(ι ⊥, false)] :: toCNF ι (p → q : Proposition At)) = true := by decide

end CSLibExtTest.Logics.Propositional.CNFNormalForm
