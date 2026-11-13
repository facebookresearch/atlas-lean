/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Models.Cost.Laws
meta import CSLibExt.Computability.Models.Cost.Basic

open CSLibExt.Cost
open Cslib.Algorithms.Lean (TimeM)

/-! Imported clients of the canonical carrier and legacy cost interface. -/

universe u

example : AddCommMonoid Cost := inferInstance
example : Monad.{u, u} CostM := inferInstance
example : LawfulMonad.{u, u} CostM := inferInstance

private def program : CostM Nat := do
  let x ← CostM.charge ⟨2, 3, 7⟩ (pure 6)
  let y ← CostM.charge ⟨5, 11, 4⟩ (pure (x + 4))
  return x + y

example : program.value = 16 := by decide
example : program.cost = ⟨7, 14, 7⟩ := by decide

/-- info: (16, { time := 7, space := 14, memory := 7 }) -/
#guard_msgs in
#eval (program.value, program.cost)

private def nested : CostM Nat :=
  CostM.charge ⟨13, 17, 6⟩ (CostM.charge ⟨19, 23, 9⟩ program)

example : nested.value = 16 := by decide
example : nested.cost = ⟨39, 54, 9⟩ := by decide
example : (CostM.pure 42).cost = Cost.zero := by decide
example : (CostM.charge Cost.zero program).cost = program.cost := by decide
example : (CostM.charge Cost.zero program).value = 16 := by decide

example : (Cost.add ⟨2, 3, 7⟩ ⟨5, 11, 4⟩) = ⟨7, 14, 7⟩ := by decide
example : (Cost.add ⟨5, 11, 4⟩ ⟨2, 3, 7⟩) = ⟨7, 14, 7⟩ := by decide
example : (Cost.add ⟨1, 2, 7⟩ ⟨3, 4, 7⟩) = ⟨4, 6, 7⟩ := by decide
example : (Cost.add Cost.zero Cost.zero) = Cost.zero := by decide
example : (3 • (⟨2, 3, 7⟩ : Cost)) = ⟨6, 9, 7⟩ := by decide
example : (0 • (⟨2, 3, 7⟩ : Cost)) = Cost.zero := by decide

example :
    (CostM.charge ⟨3, 0, 0⟩
      (CostM.charge ⟨2, 0, 0⟩ (CostM.pure 1))).cost.time = 5 := rfl

example (c₁ c₂ : Cost) : (c₁.add c₂).time = (c₂.add c₁).time :=
  Nat.add_comm _ _

-- Legacy entry points agree definitionally with the standard interface.
example (a : Nat) : CostM.pure a = (pure a : CostM Nat) := rfl
example (x : CostM Nat) (f : Nat → CostM Nat) :
    CostM.bind x f = (x >>= f) := rfl
example (a : Nat) (c : Cost) : CostM.mk a c = (⟨a, c⟩ : TimeM Cost Nat) :=
  rfl
example (x : CostM Nat) : x.value = x.ret ∧ x.cost = x.time := ⟨rfl, rfl⟩
example (x : TimeM Cost Nat) : CostM Nat := x
example (x : CostM Nat) : TimeM Cost Nat := x
example (c : Cost) (x : CostM Nat) :
    CostM.charge c x = (TimeM.tick c >>= fun _ => x) := rfl
example (x : CostM Nat) (f : Nat → CostM Nat) :
    (x >>= f).time = x.time + (f x.ret).time := TimeM.time_bind x f

private def lifted {α : Type u} (a : α) : CostM α := do
  let b ← CostM.charge ⟨1, 2, 3⟩ (pure a)
  return b

example : (lifted Nat : CostM (Type)).value = Nat := rfl
example : (lifted (Type) : CostM (Type 1)).cost = ⟨1, 2, 3⟩ := by decide
example : (CostM.bind (CostM.pure Nat) (fun _ => CostM.pure 4)).value = 4 :=
  rfl
example : (CostM.charge ⟨1, 2, 3⟩ (CostM.pure Nat)).value = Nat := rfl

example (a b c : Cost) : (a.add b).add c = a.add (b.add c) :=
  Cost.add_assoc a b c
example (a b : Cost) : a.add b = b.add a := Cost.add_comm a b
example (a : Cost) : Cost.zero.add a = a := Cost.zero_add a
example (a : Cost) : a.add Cost.zero = a := Cost.add_zero a

example {α β : Type u} (a : α) (f : α → CostM β) :
    CostM.bind (CostM.pure a) f = f a := CostM.bind_pure a f
example {α : Type u} (x : CostM α) : CostM.bind x CostM.pure = x :=
  CostM.bind_pure_right x
example {α β γ : Type u} (x : CostM α) (f : α → CostM β)
    (g : β → CostM γ) :
    CostM.bind (CostM.bind x f) g =
      CostM.bind x (fun a => CostM.bind (f a) g) := CostM.bind_assoc x f g
example {α : Type u} (a b : Cost) (x : CostM α) :
    CostM.charge a (CostM.charge b x) = CostM.charge (a.add b) x :=
  CostM.charge_charge a b x
example {α : Type u} (x : CostM α) : x >>= pure = x := bind_pure x
example {α : Type u} (x : CostM α) : id <$> x = x := id_map x

example : ((· + 1) <$> program).cost = ⟨7, 14, 7⟩ := by decide
example : ((· + 1) <$> program).value = 17 := by decide

#eval show IO Unit from do
  let rows : List (String × CostM Nat × Nat × Cost) := [
    ("pure", pure 42, 42, ⟨0, 0, 0⟩),
    ("do", program, 16, ⟨7, 14, 7⟩),
    ("nested", nested, 16, ⟨39, 54, 9⟩),
    ("zero-charge", CostM.charge Cost.zero program, 16, ⟨7, 14, 7⟩),
    ("max-right", CostM.bind (CostM.mk 2 ⟨5, 11, 4⟩)
      (fun n => CostM.charge ⟨2, 3, 7⟩ (pure (n + 1))), 3, ⟨7, 14, 7⟩),
    ("map", (· + 1) <$> program, 17, ⟨7, 14, 7⟩),
    ("seq", CostM.charge ⟨1, 2, 9⟩ (pure (· + 1)) <*> program,
      17, ⟨8, 16, 9⟩),
    ("equal-memory", CostM.charge ⟨1, 2, 7⟩ program, 16, ⟨8, 16, 7⟩)]
  for (label, result, value, cost) in rows do
    unless decide (result.value = value ∧ result.cost = cost) do
      throw (IO.userError s!"{label}: unexpected value or annotation")
    IO.println s!"{label}: {result.value}, {repr result.cost}"
