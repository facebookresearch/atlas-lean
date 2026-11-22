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

/-
# Substitution laws for certified STLC elaboration
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.ElaborationStructural
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Substitution

/-!
# Raw and intrinsic substitution agree

This module equips raw annotated terms with simultaneous substitution and
proves that it is the erasure of intrinsic simultaneous substitution.  The
proof accounts for binder lifting explicitly, including the weakening of every
substituted term below a lambda.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Ξ : List (Ty Base)}

namespace RawTm

/-- An untyped simultaneous substitution, indexed by de Bruijn positions. -/
abbrev RawSub (Base : Type u) := Nat → RawTm Base

/-- Lift a raw simultaneous substitution under one binder. -/
def liftSub (σ : RawSub Base) : RawSub Base
  | 0 => .var 0
  | n + 1 => rename Nat.succ (σ n)

/-- Apply a simultaneous substitution to a raw term. -/
def substAll (σ : RawSub Base) : RawTm Base → RawTm Base
  | .var n => σ n
  | .app f a => .app (substAll σ f) (substAll σ a)
  | .lam A body => .lam A (substAll (liftSub σ) body)

/-- The identity raw substitution. -/
def idSub : RawSub Base := .var

/-- Substitute one term for index zero and decrement all older indices. -/
def singleSub (a : RawTm Base) : RawSub Base
  | 0 => a
  | n + 1 => .var n

@[simp] theorem liftSub_zero (σ : RawSub Base) : liftSub σ 0 = .var 0 := rfl

@[simp] theorem liftSub_succ (σ : RawSub Base) (n : Nat) :
    liftSub σ (n + 1) = rename Nat.succ (σ n) := rfl

@[simp] theorem substAll_var (σ : RawSub Base) (n : Nat) :
    substAll σ (.var n) = σ n := rfl

@[simp] theorem substAll_app (σ : RawSub Base) (f a : RawTm Base) :
    substAll σ (.app f a) = .app (substAll σ f) (substAll σ a) := rfl

@[simp] theorem substAll_lam (σ : RawSub Base) (A : Ty Base) (body : RawTm Base) :
    substAll σ (.lam A body) = .lam A (substAll (liftSub σ) body) := rfl

@[simp] theorem singleSub_zero (a : RawTm Base) : singleSub a 0 = a := rfl

@[simp] theorem singleSub_succ (a : RawTm Base) (n : Nat) :
    singleSub a (n + 1) = .var n := rfl

@[simp] theorem liftSub_id : liftSub (idSub : RawSub Base) = idSub := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

@[simp] theorem substAll_id (t : RawTm Base) : substAll idSub t = t := by
  induction t with
  | var n => rfl
  | app f a ihf iha => simp [ihf, iha]
  | lam A body ih => simp [ih]

/-- Pointwise equal substitutions act equally on every raw term. -/
theorem substAll_congr {σ τ : RawSub Base} (h : ∀ n, σ n = τ n)
    (t : RawTm Base) : substAll σ t = substAll τ t := by
  induction t generalizing σ τ with
  | var n => exact h n
  | app f a ihf iha => simp [ihf h, iha h]
  | lam A body ih =>
      simp only [substAll_lam]
      congr 1
      apply ih
      intro n
      cases n with
      | zero => rfl
      | succ n => simp [h n]

/-- Renaming a raw term is substitution by renamed variables. -/
theorem rename_eq_substAll (ρ : Nat → Nat) (t : RawTm Base) :
    rename ρ t = substAll (fun n => .var (ρ n)) t := by
  induction t generalizing ρ with
  | var n => rfl
  | app f a ihf iha => simp [ihf, iha]
  | lam A body ih =>
      simp only [rename_lam, substAll_lam]
      rw [ih]
      apply congrArg (RawTm.lam A)
      apply substAll_congr
      intro n
      cases n <;> rfl

end RawTm

/-- A typed and raw simultaneous substitution agree after erasure. -/
def SubAgrees (σ : Sub Γ Δ) (s : RawTm.RawSub Base) : Prop :=
  ∀ {A} (x : Var Γ A), (σ x).erase = s x.toNat

@[simp] theorem subAgrees_id :
    SubAgrees (Sub.id : Sub Γ Γ) RawTm.idSub := by
  intro A x
  rfl

/-- Agreement is preserved by lifting both substitutions through a binder. -/
theorem SubAgrees.lift {σ : Sub Γ Δ} {s : RawTm.RawSub Base}
    (h : SubAgrees σ s) :
    SubAgrees (Sub.lift (A := A) σ) (RawTm.liftSub s) := by
  intro B x
  cases x with
  | zero => rfl
  | succ x => simp [RawTm.liftSub, Var.toNat, h x]

/-- Agreement for the one-variable intrinsic and raw substitutions. -/
theorem subAgrees_single (a : Tm Γ A) :
    SubAgrees (Sub.single a) (RawTm.singleSub a.erase) := by
  intro B x
  cases x with
  | zero => rfl
  | succ x => rfl

/-- Erasure commutes with agreeing simultaneous substitutions. -/
theorem Tm.erase_subst (σ : Sub Γ Δ) (s : RawTm.RawSub Base)
    (h : SubAgrees σ s) (t : Tm Γ A) :
    (Tm.subst σ t).erase = RawTm.substAll s t.erase := by
  induction t generalizing Δ s with
  | var x => simpa [Tm.erase] using h x
  | app f a ihf iha => simp [Tm.erase, ihf σ s h, iha σ s h]
  | @lam A B Γ body ih =>
      simp [Tm.erase, ih (Sub.lift σ) (RawTm.liftSub s) h.lift]

/-- Erasing intrinsic instantiation gives simultaneous raw substitution by
the erased argument at index zero. -/
@[simp] theorem Tm.erase_instantiate (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    (Tm.instantiate body a).erase =
      RawTm.substAll (RawTm.singleSub a.erase) body.erase := by
  rw [Tm.instantiate]
  exact Tm.erase_subst (Sub.single a) (RawTm.singleSub a.erase)
    (subAgrees_single a) body

end Cslib.Languages.LambdaCalculus.Stlc
