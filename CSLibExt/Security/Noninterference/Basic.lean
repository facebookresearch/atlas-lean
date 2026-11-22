/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Languages.IMP.BigStep
public import Mathlib.Data.Bool.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Information-flow observations for IMP

Security levels use Mathlib's Boolean lattice (`false` is low, `true` is high). Programs,
stores, expression evaluation, and terminating execution are supplied by `Cslib.IMP`.
-/

@[expose] public section

namespace Cslib.Security.Noninterference

abbrev Level := Bool
abbrev Store := IMP.State
abbrev Policy := Nat → Level

/-- Equality of all publicly observable variables. -/
def LowEquiv (Γ : Policy) (s t : Store) : Prop :=
  ∀ x, Γ x = false → s x = t x

namespace LowEquiv

@[refl] theorem refl (Γ : Policy) (s : Store) : LowEquiv Γ s s :=
  fun _ _ => rfl

@[symm] theorem symm {Γ : Policy} {s t : Store}
    (h : LowEquiv Γ s t) : LowEquiv Γ t s := fun x hx => (h x hx).symm

@[trans] theorem trans {Γ : Policy} {s t u : Store}
    (h : LowEquiv Γ s t) (h' : LowEquiv Γ t u) : LowEquiv Γ s u :=
  fun x hx => (h x hx).trans (h' x hx)

end LowEquiv

end Cslib.Security.Noninterference
