/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.PCF.Adequacy
public import CSLibExtTest.Languages.LambdaCalculus.PCF.DenotationalTests

/-!
# Tests for computational adequacy of PCF

* Adequacy turns denotations computed without evaluation into evaluations:
  `ifz zero 2 zero`, and `fix (λx. zero)` by the fixed-point equation; the
  two characterizations of `eval_numeral_iff` on `countdown 1`.
* `Ω := fix (λx : nat. x)` denotes `⊥`, so by `terminates_iff_dom` it has no
  evaluation at all, and `succ Ω` neither.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.PCF.Tests

open scoped CslibStlc
open OmegaCompletePartialOrder Tm

/-- Adequacy turns a denotation computed without evaluation into an evaluation. -/
example : Eval (.ifz .zero (numeral 2) .zero : Tm [] .nat) (numeral 2) :=
  eval_numeral_iff.mpr ifzZeroTwo_denote

/-- `fix (λx. zero)` denotes `0` by the fixed-point equation alone, so it
evaluates to `0`. -/
example : Eval fixZero (numeral 0) := by
  apply adequacy
  rw [fixZero, denote_fix, ← ContinuousHom.lfp_eq, denote_lam, denote_zero]
  exact Part.mem_some 0

/-- The two characterizations agree on `countdown 1`. -/
example : Eval (.app countdown (numeral 1)) (numeral 0) ↔
    denote (.app countdown (numeral 1)) ε = Part.some 0 :=
  eval_numeral_iff

/-- `Ω` does not terminate. -/
theorem omega_diverges : ¬ ∃ v, Eval omega v := by
  rw [terminates_iff_dom, omega_denote]
  change ¬ (Part.none : Part ℕ).Dom
  exact id

/-- `succ Ω` does not terminate either. -/
example : ¬ ∃ v, Eval (.succ omega) v := by
  rw [terminates_iff_dom]
  change ¬ ((denote omega ε : Part ℕ).map Nat.succ).Dom
  rw [omega_denote]
  change ¬ (Part.map Nat.succ (Part.none : Part ℕ)).Dom
  simp

/-- A terminating closed ground term denotes a number. -/
example : (denote fixZero ε : Part ℕ).Dom := terminates_iff_dom.mp ⟨_, fixZero_eval⟩

end Cslib.Languages.LambdaCalculus.PCF.Tests
