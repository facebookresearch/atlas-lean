/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.PCF.BigStep

/-!
# Tests for PCF syntax and evaluation

* Arithmetic and the zero test evaluate to numerals; evaluation is
  deterministic.
* `fix (λx. zero)` evaluates by one unfolding; a recursive `countdown` runs
  through two unfoldings of `fix`, exercising substitution under binders.
* Substitution leaves numerals unchanged and instantiates under a binder.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.PCF.Tests

open scoped CslibStlc
open Tm

/-- `ifz (pred (succ zero)) (succ zero) zero`. -/
def ifzExample : Tm [] .nat := .ifz (.pred (.succ .zero)) (.succ .zero) .zero

theorem ifzExample_eval : Eval ifzExample (numeral 1) :=
  .ifzZero (.predSucc (n := 0) (.succ .zero)) (.succ .zero)

/-- Evaluation is deterministic: `ifzExample` does not evaluate to `0`. -/
example : ¬ Eval ifzExample (numeral 0) := fun h =>
  absurd (numeral_injective (Eval.deterministic ifzExample_eval h)) (by decide)

/-- `pred zero` is `zero`. -/
example : Eval (.pred .zero : Tm [] .nat) .zero := .predZero .zero

/-- `fix (λx : nat. zero)`. -/
def fixZero : Tm [] .nat := .fix (.lam .zero)

theorem fixZero_eval : Eval fixZero .zero := .fix (.app .lam .zero)

/-- A recursive function: `countdown := fix (λf. λx. ifz x zero (f (pred x)))`. -/
def countdown : Tm [] (Ty.nat ⇒ Ty.nat) :=
  .fix (.lam (.lam (.ifz (.var .zero) .zero
    (.app (.var (.succ .zero)) (.pred (.var .zero))))))

/-- `countdown 1` unfolds the fixed point twice and evaluates to `zero`. -/
theorem countdown_one : Eval (.app countdown (numeral 1)) .zero :=
  .app (.fix (.app .lam .lam))
    (.ifzSucc (n := 0) (.succ .zero)
      (.app (.fix (.app .lam .lam)) (.ifzZero (.predSucc (n := 0) (.succ .zero)) .zero)))

/-- Results are values; at the ground type they are numerals. -/
example : (Tm.zero : Tm [] .nat).Value := (countdown_one.value)

example : ∃ n, (Tm.zero : Tm [] .nat) = numeral n := countdown_one.value.eq_numeral

/-- Substitution instantiates under a binder and leaves numerals alone. -/
example : (Tm.lam (.app (.var (.succ .zero)) (.var .zero)) : Tm [Ty.nat ⇒ Ty.nat] (Ty.nat ⇒ Ty.nat)).instantiate
      (.lam (.succ (.var .zero))) =
    .lam (.app (weaken (.lam (.succ (.var .zero)))) (.var .zero)) := rfl

example (σ : Sub [Ty.nat] []) : subst σ (numeral 3 : Tm [Ty.nat] .nat) = numeral 3 := by simp

/-- Renaming by the identity is the identity. -/
example (t : Tm [Ty.nat] .nat) : rename Stlc.Var.id t = t := by simp

end Cslib.Languages.LambdaCalculus.PCF.Tests
