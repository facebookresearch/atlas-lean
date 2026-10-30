/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.CPS.Simulation

/-!
# Tests for the simulation theorem of the CPS translation

* `(λx. x) (λy. y) ⇓ λy. y`; by the simulation theorem, its CPS translation run
  with a continuation that answers `λz. z` evaluates to `λz. z`, and with any
  continuation value it agrees with the continuation applied to `λy. ⟦y⟧`.
* The translation commutes with a concrete weakening and instantiation.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.CPS.SimulationTests

open scoped CslibStlc

abbrev T : Ty Unit := .base ()

/-- Answers are identity functions on the base type. -/
abbrev R : Ty Unit := T ⇒ T

/-- `λy. y : T → T`. -/
def idT : Tm [] (T ⇒ T) := .lam (.var .zero)

/-- `(λx. x) (λy. y)`, at type `T → T`. -/
def idApp : Tm [] (T ⇒ T) := .app (.lam (.var .zero)) idT

theorem idApp_eval : Eval idApp idT :=
  .app (.lam _) (.lam _) (.lam _)

/-- A continuation that ignores the value and answers `λz. z`. -/
def constK : Tm [] (cpsTy R (T ⇒ T) ⇒ R) := .lam (.lam (.var .zero))

/-- Running the CPS program with `constK` gives the answer `λz. z`. -/
example : Eval (.app (cps R idApp) constK) (.lam (.var .zero)) := by
  rw [cps_simulation_lam idApp_eval constK (.lam _)]
  exact .app (.lam _) (.lam _) (by simp [Tm.instantiate]; exact .lam _)

/-- With any continuation value, the CPS program agrees with the continuation
applied to the translated value `λy. ⟦y⟧`. -/
example (K : Tm [] (cpsTy R (T ⇒ T) ⇒ R)) (hK : Value K) (w : Tm [] R) :
    Eval (.app (cps R idApp) K) w ↔ Eval (.app K (.lam (cps R (.var .zero : Tm [T] T)))) w :=
  cps_simulation_lam idApp_eval K hK w

/-- Weakening commutes with the translation on a concrete term. -/
example : cps R (Tm.weaken (B := T) idT) = Tm.weaken (cps R idT) := cps_weaken idT

/-- Instantiation by an abstraction commutes with the translation. -/
example : cps R (Tm.instantiate (.var .zero : Tm [T ⇒ T] (T ⇒ T)) idT) =
    Tm.instantiate (cps R (.var .zero : Tm [T ⇒ T] (T ⇒ T))) (.lam (cps R (.var .zero))) :=
  cps_instantiate _ (.lam _)

end Cslib.Languages.LambdaCalculus.Stlc.CPS.SimulationTests
