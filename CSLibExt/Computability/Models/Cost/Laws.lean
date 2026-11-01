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
# Cost monad laws (Weeks 3-4 core, 90-day plan #1 COST)

`CostM` is a monad with cost accounting: `pure` costs zero, `bind`
adds costs, `charge` adds a cost. The laws below (left/right identity,
associativity, charge additivity) are what every cost analysis in the
repo may rely on; adequacy to word-RAM is the separate Weeks 3-4
deliverable (`Cost/Adequacy.lean`, L0 until proved).
-/

/-- `Cost.add` is associative. -/
theorem Cost.add_assoc (a b c : Cost) : (a.add b).add c = a.add (b.add c) := by
  cases a with | mk ta sa ma =>
  cases b with | mk tb sb mb =>
  cases c with | mk tc sc mc =>
  simp only [Cost.add]
  congr 1
  · exact Nat.add_assoc _ _ _
  · exact Nat.add_assoc _ _ _
  · omega

/-- `Cost.add` is commutative. -/
theorem Cost.add_comm (a b : Cost) : a.add b = b.add a := by
  cases a with | mk ta sa ma =>
  cases b with | mk tb sb mb =>
  simp only [Cost.add]
  congr 1
  · exact Nat.add_comm _ _
  · exact Nat.add_comm _ _
  · omega

/-- `Cost.zero` is a left identity for `Cost.add`. -/
theorem Cost.zero_add (c : Cost) : Cost.zero.add c = c := by
  cases c with | mk t s m =>
  simp [Cost.zero, Cost.add]

/-- `Cost.zero` is a right identity for `Cost.add`. -/
theorem Cost.add_zero (c : Cost) : c.add Cost.zero = c := by
  cases c with | mk t s m =>
  simp [Cost.zero, Cost.add]

/-- Left identity: binding a pure value applies the function. -/
theorem CostM.bind_pure {α β : Type} (a : α) (f : α → CostM β) :
    CostM.bind (CostM.pure a) f = f a := by
  cases hfa : f a with
  | mk v c =>
      simp only [CostM.bind, CostM.pure, hfa, Cost.zero_add]

/-- Right identity: binding with `pure` is the identity. -/
theorem CostM.bind_pure_right {α : Type} (x : CostM α) :
    CostM.bind x CostM.pure = x := by
  cases x with | mk v c =>
  simp [CostM.bind, CostM.pure, Cost.add_zero]

/-- Associativity of `bind`. -/
theorem CostM.bind_assoc {α β γ : Type} (x : CostM α) (f : α → CostM β)
    (g : β → CostM γ) :
    CostM.bind (CostM.bind x f) g =
      CostM.bind x (fun a => CostM.bind (f a) g) := by
  cases x with | mk v c =>
  cases f v with | mk v₂ c₂ =>
  cases g v₂ with | mk v₃ c₃ =>
  simp [CostM.bind, Cost.add_assoc]

/-- Charging twice is charging the sum. -/
theorem CostM.charge_charge {α : Type} (c₁ c₂ : Cost) (x : CostM α) :
    CostM.charge c₁ (CostM.charge c₂ x) = CostM.charge (c₁.add c₂) x := by
  cases x with | mk v c =>
  simp [CostM.charge, Cost.add_assoc]

end CSLibExt.Cost
