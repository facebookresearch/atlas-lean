/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.CPS.CallByNameSimulation

/-!
# Tests for the simulation theorem of the call-by-name CPS translation

* `(λx. λy. y) ((λz. z) (λz. z))` evaluates by name to `λy. y` without
  evaluating its argument (the `EvalN` derivation has no premise about it);
  by the simulation theorem, its translation run by value with a continuation
  that answers `λz. z` evaluates to `λz. z`, and with any continuation value it
  agrees with the continuation applied to `λy. ⟦y⟧`.
* Closed translated terms are values, and instantiation commutes with the
  translation on a concrete term.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.CPS.CbnSimulationTests

open scoped CslibStlc

abbrev T : Ty Unit := .base ()

/-- Answers are identity functions on the base type. -/
abbrev R : Ty Unit := T ⇒ T

/-- `λz. z : T → T`. -/
def idT : Tm [] (T ⇒ T) := .lam (.var .zero)

/-- `λx. λy. y`, ignoring its first argument. -/
def second : Tm [] ((T ⇒ T) ⇒ (T ⇒ T) ⇒ (T ⇒ T)) := .lam (.lam (.var .zero))

/-- `(λx. λy. y) ((λz. z) (λz. z))`. -/
def prog : Tm [] ((T ⇒ T) ⇒ (T ⇒ T)) := .app second (.app (.lam (.var .zero)) idT)

/-- By-name evaluation of `prog`: the argument `(λz. z) (λz. z)` is never
evaluated. -/
theorem prog_evalN : EvalN prog (.lam (.var .zero)) :=
  .app (.lam _) (.lam _)

/-- A continuation that ignores the value and answers `λz. z`. -/
def constK : Tm [] (cbnTy R ((T ⇒ T) ⇒ (T ⇒ T)) ⇒ R) := .lam (Tm.weaken idT)

/-- Running the translation of `prog` by value with `constK` answers `λz. z`. -/
example : Eval (.app (cbn R prog) constK) idT := by
  rw [cbn_simulation prog_evalN constK (.lam _)]
  exact .app (.lam _) (.lam _) (by simp [Tm.instantiate, idT]; exact .lam _)

/-- With any continuation value, the translated program agrees with the
continuation applied to the translated value `λy. ⟦y⟧`. -/
example (K : Tm [] (cbnTy R ((T ⇒ T) ⇒ (T ⇒ T)) ⇒ R)) (hK : Value K) (w : Tm [] R) :
    Eval (.app (cbn R prog) K) w ↔
      Eval (.app K (.lam (cbn R (.var .zero : Tm [T ⇒ T] (T ⇒ T))))) w :=
  cbn_simulation prog_evalN K hK w

/-- The translation of a closed application is a value (an abstraction over the
continuation), so it can be passed unevaluated. -/
example : Value (cbn R prog) := cbn_value prog

/-- Instantiation commutes with the translation: the argument's translation is
substituted for the variable. -/
example : cbn R (Tm.instantiate (.var .zero : Tm [T ⇒ T] (T ⇒ T)) idT) =
    Tm.instantiate (cbn R (.var .zero : Tm [T ⇒ T] (T ⇒ T))) (cbn R idT) :=
  cbn_instantiate _ _

end Cslib.Languages.LambdaCalculus.Stlc.CPS.CbnSimulationTests
