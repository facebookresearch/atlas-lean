/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.References.Divergence

/-!
# Tests for Landin's knot

* The knot is well typed at `Unit` and diverges: no value is reachable, and
  every reachable configuration steps.
* The configuration `(!l₀) unit` with `λx. (!l₀) x` stored at `l₀` returns to
  itself through the two explicit steps of `knot_cycle`, and the knot reaches it
  through the four explicit steps of `knot_prefix`; each step is the unique one
  (determinism), so no shorter path exists.
* Store typing of the cycle: the stored function has type `Unit → Unit`.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.References.DivergenceTests

open Knot

example : HasType ([] : List (Ty Unit)) [] (knot : Term Unit) .unit := knot_hasType

example : ¬ ∃ (v : Term Unit) (μ : Store Unit), Steps knot [] v μ ∧ v.Value :=
  knot_diverges

/-- The cycle: two steps from `(!l₀) unit` back to itself, and `(!l₀) unit`
does not step to itself directly. -/
example : Steps (loopA : Term Unit) [body₀] loopA [body₀] :=
  (Steps.single knot_cycle.1).tail knot_cycle.2

example : ¬ Step (loopA : Term Unit) [body₀] loopA [body₀] := fun h => by
  have := (Step.deterministic h stepA).1
  cases this

/-- Four steps from the start into the cycle. -/
theorem knot_reaches_loop : Steps (knot : Term Unit) [] loopA [body₀] :=
  let ⟨h₀, h₁, h₂, h₃⟩ := knot_prefix (Base := Unit)
  (Steps.single h₀).tail h₁ |>.tail h₂ |>.tail h₃

/-- The stored function is well typed, so the store in the cycle is well typed
under the store typing `[Unit → Unit]`. -/
example : StoreTyped ([] : List (Ty Unit)) [.arr .unit .unit] [body₀] :=
  List.Forall₂.cons ⟨.lam _ _, .lam (.app (.deref (.loc rfl)) (.var rfl))⟩ .nil

/-- Running forever: some step exists after reaching the cycle. -/
example : ∃ (t : Term Unit) (μ : Store Unit), Step loopA [body₀] t μ :=
  knot_runs_forever knot_reaches_loop

end Cslib.Languages.LambdaCalculus.References.DivergenceTests
