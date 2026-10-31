/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

@[expose] public section

namespace CSLibExt.Cost

/-!
# Cost monad (Week 2 skeleton, 90-day plan #1 COST)

The single cost-accounting monad all verified algorithms will use:
time steps, space cells, peak memory. Adequacy to word-RAM is a
Weeks 3–4 deliverable (statement lives in `Cost/Adequacy.lean`, L0 until
proved). This is NOT a complexity class, a TM model, or a replacement for
`TimeM` (whose `time` field is unverified).

Assurance: definitions + examples below are kernel-checked standalone
under Lean v4.35.0. No `sorry`, no axioms beyond Lean core.
-/

/-- Cost accounting: time steps, space cells, peak memory. All `Nat`. -/
structure Cost where
  time : Nat
  space : Nat
  memory : Nat
  deriving DecidableEq, Repr

/-- Zero cost. -/
def Cost.zero : Cost := ⟨0, 0, 0⟩

/-- Sequential composition: costs add componentwise. -/
def Cost.add (c₁ c₂ : Cost) : Cost :=
  ⟨c₁.time + c₂.time, c₁.space + c₂.space, max c₁.memory c₂.memory⟩

/-- The cost monad: a value plus the cost of producing it. -/
structure CostM (α : Type) where
  value : α
  cost : Cost

/-- Pure: no cost. -/
def CostM.pure (a : α) : CostM α := ⟨a, Cost.zero⟩

/-- Sequential composition: run `x`, then `f` on its value, adding costs. -/
def CostM.bind (x : CostM α) (f : α → CostM β) : CostM β :=
  let y := f x.value
  ⟨y.value, x.cost.add y.cost⟩

/-- Charge `c` to a computation. -/
def CostM.charge (c : Cost) (x : CostM α) : CostM α :=
  ⟨x.value, c.add x.cost⟩

/-- Worked example: charging 3 time steps, then 2 more, costs 5. -/
example :
    (CostM.charge ⟨3, 0, 0⟩
      (CostM.charge ⟨2, 0, 0⟩ (CostM.pure 1))).cost.time = 5 := rfl

/-- Worked example: `Cost.add` is commutative on time. -/
example (c₁ c₂ : Cost) : (c₁.add c₂).time = (c₂.add c₁).time := Nat.add_comm _ _

end CSLibExt.Cost
