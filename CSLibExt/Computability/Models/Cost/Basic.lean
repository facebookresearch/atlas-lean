/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM

@[expose] public section

namespace CSLibExt.Cost

/-!
# Resource annotations via CSLib's `TimeM`

Time and cumulative space annotations add under sequential composition.
Supplied peak-memory annotations combine by maximum, not by addition.
These annotations are trusted: no theorem here relates them to hardware
execution time, retained allocations, or a word-RAM operational semantics.

## CSLib reuse and portability

The pinned `Cslib.Algorithms.Lean.TimeM` already supplies a polymorphic
carrier and the standard monad API. `CostM` specializes it to `Cost`, whose
addition has the laws needed by the inherited `LawfulMonad` instance.
The legacy `value`, `cost`, `mk`, `pure`, and `bind` names are compatibility
entry points; new clients can use `ret`, `time`, and standard do notation.
Record literals and updates use the upstream field names `ret` and `time`.
No separate computation carrier or conversion is needed to use CSLib APIs.
-/

-- Preserve the existing public `CSLibExt.Cost.Cost` namespace.
set_option linter.dupNamespace false

/-- Trusted time, cumulative space, and peak-memory annotations. -/
structure Cost where
  time : Nat
  space : Nat
  memory : Nat
  deriving DecidableEq, Repr

/-- Zero cost. -/
def Cost.zero : Cost := ⟨0, 0, 0⟩

/-- Add time and cumulative space; take the maximum supplied memory. -/
def Cost.add (c₁ c₂ : Cost) : Cost :=
  ⟨c₁.time + c₂.time, c₁.space + c₂.space, max c₁.memory c₂.memory⟩

/-- `Cost.add` is associative. -/
theorem Cost.add_assoc (a b c : Cost) :
    (a.add b).add c = a.add (b.add c) := by
  cases a; cases b; cases c
  simp only [Cost.add, Nat.add_assoc, Nat.max_assoc]

/-- `Cost.add` is commutative. -/
theorem Cost.add_comm (a b : Cost) : a.add b = b.add a := by
  cases a; cases b
  simp only [Cost.add, Nat.add_comm, Nat.max_comm]

/-- `Cost.zero` is a left identity for `Cost.add`. -/
theorem Cost.zero_add (c : Cost) : Cost.zero.add c = c := by
  cases c
  simp [Cost.zero, Cost.add]

/-- `Cost.zero` is a right identity for `Cost.add`. -/
theorem Cost.add_zero (c : Cost) : c.add Cost.zero = c := by
  cases c
  simp [Cost.zero, Cost.add]

instance : AddZero Cost where
  zero := Cost.zero
  add := Cost.add

/-- Resource annotations form a commutative additive monoid. -/
instance : AddCommMonoid Cost where
  add_assoc := Cost.add_assoc
  zero_add := Cost.zero_add
  add_zero := Cost.add_zero
  add_comm := Cost.add_comm
  nsmul := nsmulRec

open Cslib.Algorithms.Lean (TimeM)

universe u v

/-- CSLib's polymorphic computation carrier with resource annotations. -/
abbrev CostM (α : Type u) := TimeM Cost α

/-- Legacy constructor; record literals use upstream `ret` and `time`. -/
abbrev CostM.mk {α : Type u} (value : α) (cost : Cost) : CostM α :=
  ⟨value, cost⟩

/-- Legacy observation of the return value (`TimeM.ret`). -/
abbrev CostM.value {α : Type u} (x : CostM α) : α := x.ret

/-- Legacy observation of the resource annotation (`TimeM.time`). -/
abbrev CostM.cost {α : Type u} (x : CostM α) : Cost := x.time

/-- Legacy zero-cost entry point; prefer standard `pure` in new clients. -/
abbrev CostM.pure {α : Type u} (a : α) : CostM α := TimeM.pure a

/-- Legacy sequential composition; prefer `>>=` in new clients. -/
abbrev CostM.bind {α : Type u} {β : Type v}
    (x : CostM α) (f : α → CostM β) : CostM β := TimeM.bind x f

/-- Charge `c` before a computation, using CSLib's tick and bind. -/
def CostM.charge {α : Type u} (c : Cost) (x : CostM α) : CostM α :=
  TimeM.tick c >>= fun _ => x

end CSLibExt.Cost
