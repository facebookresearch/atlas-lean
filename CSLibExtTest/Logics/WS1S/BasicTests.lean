/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.WS1S.Basic
public meta import CSLibExt.Logics.WS1S.Basic
public meta import Mathlib.Data.Nat.Pairing

/-!
# Tests for WS1S syntax, semantics and Gödel numbering

* Regression examples for the collisions of an earlier numbering: `.zero` and `.var 1` both had
  code `1`, and `falsum` had code `3 = codeWS1S (.lt (.var 0) (.var 1))`.
* The numberings evaluate to the expected Cantor-pairing codes, by `decide` and by `#guard`.
* `Holds` on closed formulas: `∀ x, x < x + 1` holds, `∀ x, x = 0` does not, and the set
  quantifier ranges over finite sets.
-/

@[expose] public section

namespace Cslib.Logic.WS1S.Tests

/-! ## Gödel numbering -/

/-- The earlier numbering gave `codeWS1STerm .zero = 1 = codeWS1STerm (.var 1)`, so the valid
`.eq .zero .zero` and the invalid `.eq .zero (.var 1)` shared a code; the tags separate them. -/
example : codeWS1STerm .zero ≠ codeWS1STerm (.var 1) := by decide

example : codeWS1S (.eq .zero .zero) ≠ codeWS1S (.eq .zero (.var 1)) := by decide

/-- The earlier bare code `3` of `falsum` was the code of `.lt (.var 0) (.var 1)`
(`Nat.pair 1 (Nat.pair 0 1) = Nat.pair 1 1 = 3`). -/
example : codeWS1S (.lt (.var 0) (.var 1)) = 3 := by decide

example : codeWS1S .falsum ≠ codeWS1S (.lt (.var 0) (.var 1)) := by decide

example : codeWS1STerm (.var 1) = 1 := by decide

example : codeWS1STerm .zero = 2 := by decide

example : codeWS1STerm (.succ .zero) = Nat.pair 2 2 := by decide

example : codeWS1S .falsum = 12 := by decide

#guard codeWS1S (.imp .falsum .falsum) == Nat.pair 4 (Nat.pair 12 12)

#guard codeWS1S (.all (.mem (.var 0) 0)) == Nat.pair 5 (Nat.pair 2 (Nat.pair 0 0))

#guard codeWS1S (.allSet .falsum) != codeWS1S (.all .falsum)

/-! ## Semantics -/

/-- `∀ x, x < x + 1`. -/
example : (WS1SFormula.all (.lt (.var 0) (.succ (.var 0)))).Holds (fun _ => 0) (fun _ => ∅) :=
  fun x => Nat.lt_succ_self x

/-- `∀ x, x = 0` fails at `x = 1`. -/
example : ¬ (WS1SFormula.all (.eq (.var 0) .zero)).Holds (fun _ => 0) (fun _ => ∅) :=
  fun h => absurd (h 1) (by simp [WS1SFormula.Holds, WS1STerm.eval])

/-- `∃ X, 0 ∈ X`, witnessed by `{0}`. -/
example : (WS1SFormula.exSet (.mem .zero 0)).Holds (fun _ => 0) (fun _ => ∅) :=
  fun h => h {0} (by simp [WS1SFormula.Holds, WS1STerm.eval])

/-- Weakness: no finite set contains every natural, so `∃ X, ∀ x, x ∈ X` fails. -/
example : ¬ (WS1SFormula.exSet (.all (.mem (.var 0) 0))).Holds (fun _ => 0) (fun _ => ∅) := by
  intro h
  apply h
  intro X hX
  exact (Finset.exists_nat_subset_range X).elim fun n hn =>
    absurd (hn (hX n)) (by simp [WS1STerm.eval])

end Cslib.Logic.WS1S.Tests
