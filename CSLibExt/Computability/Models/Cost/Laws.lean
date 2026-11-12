/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Models.Cost.Basic

@[expose] public section

namespace CSLibExt.Cost

/-!
# Resource annotation laws

The legacy `CostM` laws below specialize CSLib's lawful-monad interface.
Time and cumulative space add; supplied peak memory combines by maximum.
These are annotation laws, not adequacy results for an operational model.
The `Cost` component laws and instances are available from `Basic` alone.
-/

universe u

/-- Left identity: binding a pure value applies the function. -/
theorem CostM.bind_pure {α β : Type u} (a : α) (f : α → CostM β) :
    CostM.bind (CostM.pure a) f = f a := pure_bind a f

/-- Right identity: binding with `pure` is the identity. -/
theorem CostM.bind_pure_right {α : Type u} (x : CostM α) :
    CostM.bind x CostM.pure = x := _root_.bind_pure x

/-- Associativity of `bind`. -/
theorem CostM.bind_assoc {α β γ : Type u} (x : CostM α)
    (f : α → CostM β) (g : β → CostM γ) :
    CostM.bind (CostM.bind x f) g =
      CostM.bind x (fun a => CostM.bind (f a) g) :=
  LawfulMonad.bind_assoc x f g

/-- Charging twice combines annotations by `Cost.add`. -/
theorem CostM.charge_charge {α : Type u} (c₁ c₂ : Cost) (x : CostM α) :
    CostM.charge c₁ (CostM.charge c₂ x) =
      CostM.charge (c₁.add c₂) x :=
  Cslib.Algorithms.Lean.TimeM.ext rfl (Cost.add_assoc c₁ c₂ x.cost).symm

end CSLibExt.Cost
