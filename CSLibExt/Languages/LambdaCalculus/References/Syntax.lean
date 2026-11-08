/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The simply typed lambda calculus with references: syntax
-/
module

public import Mathlib.Data.List.Basic

/-!
# The simply typed lambda calculus with references: syntax

This file defines the syntax of the simply typed lambda calculus with mutable
references of Pierce, *Types and Programming Languages* (MIT Press, 2002),
Chapter 13, Figure 13-1: function types, `Unit`, and reference types `Ref T`,
with allocation `ref t`, dereferencing `!t`, assignment `t₁ := t₂`, and store
locations `l`. Base types are a parameter, as in the de Bruijn STLC in
`../DeBruijn/Stlc/`.

Terms are extrinsically typed and use de Bruijn indices for variables. Store
locations are natural numbers indexing the store; they are not variables, so
renaming and substitution leave them unchanged. Renaming and substitution are
parallel (simultaneous) operations given by functions on indices.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.References

universe u

/-- Types of the simply typed lambda calculus with references. -/
inductive Ty (Base : Type u) where
  /-- An uninterpreted base type. -/
  | base : Base → Ty Base
  /-- The unit type. -/
  | unit : Ty Base
  /-- Function types. -/
  | arr : Ty Base → Ty Base → Ty Base
  /-- Reference cells holding values of the given type. -/
  | ref : Ty Base → Ty Base
  deriving DecidableEq, Repr

/-- Terms with de Bruijn variables and natural-number store locations. -/
inductive Term (Base : Type u) where
  /-- A de Bruijn variable. -/
  | var : Nat → Term Base
  /-- A lambda abstraction annotated with its parameter type. -/
  | lam : Ty Base → Term Base → Term Base
  /-- Application. -/
  | app : Term Base → Term Base → Term Base
  /-- The unit value. -/
  | unit : Term Base
  /-- A store location. Locations arise during evaluation, not in source
  programs. -/
  | loc : Nat → Term Base
  /-- Allocation of a fresh reference cell, `ref t`. -/
  | ref : Term Base → Term Base
  /-- Dereferencing, `!t`. -/
  | deref : Term Base → Term Base
  /-- Assignment, `t₁ := t₂`. -/
  | assign : Term Base → Term Base → Term Base
  deriving DecidableEq, Repr

variable {Base : Type u}

namespace Term

/-- Values: abstractions, unit, and store locations. -/
inductive Value : Term Base → Prop
  | lam (T : Ty Base) (body : Term Base) : Value (.lam T body)
  | unit : Value .unit
  | loc (l : Nat) : Value (.loc l)

/-- Extend a variable renaming under one binder. -/
def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | x + 1 => ρ x + 1

/-- Apply a variable renaming to a term. Locations are unchanged. -/
def rename : (Nat → Nat) → Term Base → Term Base
  | ρ, .var x => .var (ρ x)
  | ρ, .lam T body => .lam T (rename (liftRen ρ) body)
  | ρ, .app f a => .app (rename ρ f) (rename ρ a)
  | _, .unit => .unit
  | _, .loc l => .loc l
  | ρ, .ref t => .ref (rename ρ t)
  | ρ, .deref t => .deref (rename ρ t)
  | ρ, .assign t₁ t₂ => .assign (rename ρ t₁) (rename ρ t₂)

/-- Extend a substitution under one binder. -/
def liftSub (σ : Nat → Term Base) : Nat → Term Base
  | 0 => .var 0
  | x + 1 => rename Nat.succ (σ x)

/-- Apply a parallel substitution to a term. Locations are unchanged. -/
def subst : (Nat → Term Base) → Term Base → Term Base
  | σ, .var x => σ x
  | σ, .lam T body => .lam T (subst (liftSub σ) body)
  | σ, .app f a => .app (subst σ f) (subst σ a)
  | _, .unit => .unit
  | _, .loc l => .loc l
  | σ, .ref t => .ref (subst σ t)
  | σ, .deref t => .deref (subst σ t)
  | σ, .assign t₁ t₂ => .assign (subst σ t₁) (subst σ t₂)

/-- The substitution replacing variable `0` by `s` and lowering every other
variable by one. -/
def singleSub (s : Term Base) : Nat → Term Base
  | 0 => s
  | x + 1 => .var x

/-- Substitute `s` for variable `0` in `t`, written `[0 ↦ s] t` in TAPL. -/
def instantiate (t s : Term Base) : Term Base :=
  subst (singleSub s) t

@[simp] theorem liftRen_zero (ρ : Nat → Nat) : liftRen ρ 0 = 0 := rfl

@[simp] theorem liftRen_succ (ρ : Nat → Nat) (x : Nat) :
    liftRen ρ (x + 1) = ρ x + 1 := rfl

@[simp] theorem liftSub_zero (σ : Nat → Term Base) : liftSub σ 0 = .var 0 := rfl

@[simp] theorem liftSub_succ (σ : Nat → Term Base) (x : Nat) :
    liftSub σ (x + 1) = rename Nat.succ (σ x) := rfl

@[simp] theorem singleSub_zero (s : Term Base) : singleSub s 0 = s := rfl

@[simp] theorem singleSub_succ (s : Term Base) (x : Nat) :
    singleSub s (x + 1) = .var x := rfl

end Term

end Cslib.Languages.LambdaCalculus.References
