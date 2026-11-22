/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Structural laws for certified STLC elaboration
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Elaboration

/-!
# Structural laws for raw STLC terms

This module relates structural operations on the extrinsic surface language to
the corresponding intrinsically typed operations.  The main result states
that erasure commutes with any type-preserving variable renaming whose action
on de Bruijn indices is known.  Weakening is obtained as a direct corollary.

Separating these laws from the elaborator keeps the executable checker small
while giving downstream developments a reusable interface for moving checked
programs between contexts.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Ξ : List (Ty Base)}

namespace RawTm

/-- Lift a numerical renaming through one binder. -/
def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Apply a de Bruijn-index renaming, lifting it at every binder. -/
def rename (ρ : Nat → Nat) : RawTm Base → RawTm Base
  | .var n => .var (ρ n)
  | .app f a => RawTm.app (rename ρ f) (rename ρ a)
  | .lam A body => RawTm.lam A (rename (liftRen ρ) body)

@[simp] theorem liftRen_zero (ρ : Nat → Nat) : liftRen ρ 0 = 0 := rfl

@[simp] theorem liftRen_succ (ρ : Nat → Nat) (n : Nat) :
    liftRen ρ (n + 1) = ρ n + 1 := rfl

@[simp] theorem liftRen_id : liftRen id = id := by
  funext n
  cases n <;> rfl

/-- Lifting distributes over composition. -/
theorem liftRen_comp (ρ σ : Nat → Nat) :
    liftRen (σ ∘ ρ) = liftRen σ ∘ liftRen ρ := by
  funext n
  cases n <;> rfl

@[simp] theorem rename_var (ρ : Nat → Nat) (n : Nat) :
    rename ρ (RawTm.var n : RawTm Base) = RawTm.var (ρ n) := rfl

@[simp] theorem rename_app (ρ : Nat → Nat) (f a : RawTm Base) :
    rename ρ (RawTm.app f a) = RawTm.app (rename ρ f) (rename ρ a) := rfl

@[simp] theorem rename_lam (ρ : Nat → Nat) (A : Ty Base) (body : RawTm Base) :
    rename ρ (RawTm.lam A body) = RawTm.lam A (rename (liftRen ρ) body) := rfl

@[simp] theorem rename_id (t : RawTm Base) : rename id t = t := by
  induction t with
  | var n => rfl
  | app f a ihf iha => simp [ihf, iha]
  | lam A body ih => simp [ih]

/-- Numerical renamings compose extensionally on raw syntax. -/
theorem rename_comp (ρ σ : Nat → Nat) (t : RawTm Base) :
    rename σ (rename ρ t) = rename (σ ∘ ρ) t := by
  induction t generalizing ρ σ with
  | var n => rfl
  | app f a ihf iha => simp [ihf, iha]
  | lam A body ih =>
      simp only [rename_lam]
      rw [ih, liftRen_comp]

/-- Renaming preserves the number of syntax nodes. -/
@[simp] theorem size_rename (ρ : Nat → Nat) (t : RawTm Base) :
    (rename ρ t).size = t.size := by
  induction t generalizing ρ with
  | var n => rfl
  | app f a ihf iha => simp [RawTm.size, ihf, iha]
  | lam A body ih => simp [RawTm.size, ih]

/-- Shifting preserves the number of syntax nodes. -/
@[simp] theorem size_shift (amount cutoff : Nat) (t : RawTm Base) :
    (t.shift amount cutoff).size = t.size := by
  induction t generalizing cutoff with
  | var n => simp [RawTm.shift, RawTm.size]
  | app f a ihf iha => simp [RawTm.shift, RawTm.size, ihf, iha]
  | lam A body ih => simp [RawTm.shift, RawTm.size, ih]

/-- List the indices occurring in a raw term.  This intentionally includes
bound occurrences and is useful for diagnostics rather than scoping. -/
def indices : RawTm Base → List Nat
  | .var n => [n]
  | .app f a => indices f ++ indices a
  | .lam _ body => indices body

@[simp] theorem indices_var (n : Nat) :
    indices (RawTm.var n : RawTm Base) = [n] := rfl

@[simp] theorem indices_app (f a : RawTm Base) :
    indices (RawTm.app f a) = indices f ++ indices a := rfl

@[simp] theorem indices_lam (A : Ty Base) (body : RawTm Base) :
    indices (RawTm.lam A body) = indices body := rfl

/-- The free indices at binder depth `depth`. -/
def freeIndices : Nat → RawTm Base → List Nat
  | depth, .var n => if depth ≤ n then [n - depth] else []
  | depth, .app f a => freeIndices depth f ++ freeIndices depth a
  | depth, .lam _ body => freeIndices (depth + 1) body

/-- A raw term is closed when it has no free indices. -/
def Closed (t : RawTm Base) : Prop := freeIndices 0 t = []

instance (t : RawTm Base) : Decidable t.Closed := by
  unfold Closed
  infer_instance

@[simp] theorem freeIndices_var_zero (n : Nat) :
    freeIndices 0 (RawTm.var n : RawTm Base) = [n] := by
  simp [freeIndices]

@[simp] theorem freeIndices_app (depth : Nat) (f a : RawTm Base) :
    freeIndices depth (RawTm.app f a) =
      freeIndices depth f ++ freeIndices depth a := rfl

@[simp] theorem freeIndices_lam (depth : Nat) (A : Ty Base) (body : RawTm Base) :
    freeIndices depth (RawTm.lam A body) = freeIndices (depth + 1) body := rfl

@[simp] theorem closed_app (f a : RawTm Base) :
    Closed (RawTm.app f a) ↔ Closed f ∧ Closed a := by
  simp [Closed, freeIndices]

end RawTm

/-- A typed renaming and a numerical renaming agree when erasing every
well-typed variable gives the prescribed numerical image. -/
def RenAgrees (ρ : Ren Γ Δ) (r : Nat → Nat) : Prop :=
  ∀ {A} (x : Var Γ A), (ρ x).toNat = r x.toNat

@[simp] theorem renAgrees_id : RenAgrees (Var.id : Ren Γ Γ) id := by
  intro A x
  rfl

/-- Agreement is preserved when both renamings are lifted under a binder. -/
theorem RenAgrees.lift {ρ : Ren Γ Δ} {r : Nat → Nat} (h : RenAgrees ρ r) :
    RenAgrees (Var.lift (A := A) ρ) (RawTm.liftRen r) := by
  intro B x
  cases x with
  | zero => rfl
  | succ x => simp [RawTm.liftRen, Var.toNat, h x]

/-- Agreement is closed under composition. -/
theorem RenAgrees.comp {ρ : Ren Γ Δ} {r : Nat → Nat}
    {σ : Ren Δ Ξ} {s : Nat → Nat}
    (hρ : RenAgrees ρ r) (hσ : RenAgrees σ s) :
    RenAgrees (Var.comp ρ σ) (s ∘ r) := by
  intro A x
  exact (hσ (ρ x)).trans (congrArg s (hρ x))

/-- Erasure commutes with every agreeing typed/raw renaming pair. -/
theorem Tm.erase_rename (ρ : Ren Γ Δ) (r : Nat → Nat)
    (h : RenAgrees ρ r) (t : Tm Γ A) :
    (Tm.rename ρ t).erase = RawTm.rename r t.erase := by
  induction t generalizing Δ r with
  | var x => simp [Tm.erase, h x]
  | app f a ihf iha => simp [Tm.erase, ihf ρ r h, iha ρ r h]
  | @lam A B Γ body ih =>
      simp [Tm.erase, ih (Var.lift ρ) (RawTm.liftRen r) h.lift]

/-- Weakening an intrinsic term erases to incrementing all its free raw
indices. -/
@[simp] theorem Tm.erase_weaken (t : Tm Γ A) :
    (Tm.weaken (B := B) t).erase = RawTm.rename Nat.succ t.erase := by
  apply Tm.erase_rename
  intro C x
  rfl

/-- Two agreeing presentations of the same intrinsic renaming act identically
on every erased well-typed term. -/
theorem RawTm.rename_eq_on_erase (ρ : Ren Γ Δ) (r s : Nat → Nat)
    (hr : RenAgrees ρ r) (hs : RenAgrees ρ s) (t : Tm Γ A) :
    RawTm.rename r t.erase = RawTm.rename s t.erase := by
  rw [← Tm.erase_rename ρ r hr, ← Tm.erase_rename ρ s hs]

end Cslib.Languages.LambdaCalculus.Stlc
