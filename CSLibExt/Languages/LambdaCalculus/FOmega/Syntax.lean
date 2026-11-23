/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.List.Defs

/-! # Intrinsically kinded type operators for pure Fω

An ordered kind telescope uses the newest variable at its head. Kinding and
scope are indices; no malformed operator application is representable.
This is the project-authored pure Fω presentation, not the bounded Fsub syntax.

The kinds and type constructors follow the standard Fω rules in Atkey's
Section 2, Figure 1, and Pierce's Chapters 29-30. Here named variables and
extrinsic kinding are replaced by intrinsically kinded de Bruijn syntax.
The continuation uses beta-only type conversion, not Atkey's beta-eta theory;
no additional data kinds, subtyping or recursion are included.

## References

* Benjamin C. Pierce, *Types and Programming Languages*, MIT Press (2002),
  Chapters 29, "Type Operators and Kinding", and 30, "Higher-Order Polymorphism".
* Robert Atkey, *Relational Parametricity for Higher Kinds*, CSL 2012,
  pp. 46-61, Section 2. https://doi.org/10.4230/LIPIcs.CSL.2012.46.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega

/-- Kinds of pure Fω. `star` classifies types of terms. -/
inductive Kind where
  | star : Kind
  | arrow : Kind → Kind → Kind
  deriving DecidableEq, Repr

/-- A type variable with its position and kind certified by the telescope. -/
inductive KVar : List Kind → Kind → Type where
  | zero {Δ : List Kind} {κ : Kind} : KVar (κ :: Δ) κ
  | succ {Δ : List Kind} {κ μ : Kind} : KVar Δ κ → KVar (μ :: Δ) κ

/-- Kind-preserving renamings of type variables. -/
abbrev KRen (Δ Ε : List Kind) := ∀ {κ}, KVar Δ κ → KVar Ε κ

namespace KRen

/-- Lift a kind-preserving renaming beneath a type binder. -/
def lift {Δ Ε : List Kind} {μ : Kind} (ρ : KRen Δ Ε) :
    KRen (μ :: Δ) (μ :: Ε)
  | _, .zero => .zero
  | _, .succ x => .succ (ρ x)

end KRen

/-- Type operators, intrinsically indexed by context and result kind. -/
inductive Ty : List Kind → Kind → Type where
  | var {Δ : List Kind} {κ : Kind} : KVar Δ κ → Ty Δ κ
  | lam {Δ : List Kind} {κ μ : Kind} :
      Ty (κ :: Δ) μ → Ty Δ (.arrow κ μ)
  | app {Δ : List Kind} {κ μ : Kind} :
      Ty Δ (.arrow κ μ) → Ty Δ κ → Ty Δ μ
  | arr {Δ : List Kind} : Ty Δ .star → Ty Δ .star → Ty Δ .star
  | all {Δ : List Kind} {κ : Kind} : Ty (κ :: Δ) .star → Ty Δ .star

namespace Ty

/-- Rename free type variables, lifting at both forms of type binder. -/
def rename {Δ Ε : List Kind} (ρ : KRen Δ Ε) :
    {κ : Kind} → Ty Δ κ → Ty Ε κ
  | _, .var x => .var (ρ x)
  | _, .lam b => .lam (rename (KRen.lift ρ) b)
  | _, .app f a => .app (rename ρ f) (rename ρ a)
  | _, .arr a b => .arr (rename ρ a) (rename ρ b)
  | _, .all b => .all (rename (KRen.lift ρ) b)

/-- Kind-preserving simultaneous substitutions. -/
abbrev Sub (Δ Ε : List Kind) := ∀ {κ}, KVar Δ κ → Ty Ε κ

/-- Lift substitution beneath a type binder without capturing old images. -/
def liftSub {Δ Ε : List Kind} {μ : Kind} (σ : Sub Δ Ε) :
    Sub (μ :: Δ) (μ :: Ε)
  | _, .zero => .var .zero
  | _, .succ x => rename KVar.succ (σ x)

/-- Capture-avoiding simultaneous substitution of kinded type operators. -/
def subst {Δ Ε : List Kind} (σ : Sub Δ Ε) :
    {κ : Kind} → Ty Δ κ → Ty Ε κ
  | _, .var x => σ x
  | _, .lam b => .lam (subst (liftSub σ) b)
  | _, .app f a => .app (subst σ f) (subst σ a)
  | _, .arr a b => .arr (subst σ a) (subst σ b)
  | _, .all b => .all (subst (liftSub σ) b)

/-- Substitution replacing only the newest type variable. -/
def single {Δ : List Kind} {κ : Kind} (a : Ty Δ κ) : Sub (κ :: Δ) Δ
  | _, .zero => a
  | _, .succ x => .var x

/-- Substitute for the newest variable and discharge its binder. -/
def instantiate {Δ : List Kind} {κ μ : Kind}
    (b : Ty (κ :: Δ) μ) (a : Ty Δ κ) : Ty Δ μ := subst (single a) b

end Ty

end Cslib.Languages.LambdaCalculus.FOmega
