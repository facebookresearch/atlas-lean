/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

/-!
# Curry-Howard: STLC typing to natural deduction

Simple types double as implicational propositions. This module
defines natural-deduction provability and simply typed lambda
terms, and proves the soundness direction of the Curry-Howard
correspondence: every typed term yields a proof of its type.
The converse direction is not formalized here.
-/

@[expose] public section

/-- Simple types = implicational propositions (Curry-Howard
core of VER-24). -/
inductive Ty : Type
  | atom (n : ℕ) : Ty
  | imp (A B : Ty) : Ty
deriving DecidableEq

/-- Natural deduction provability from a context (list of
assumptions). -/
inductive ND : List Ty → Ty → Prop
  | hyp {Γ : List Ty} {A : Ty} (h : A ∈ Γ) : ND Γ A
  | impI {Γ : List Ty} {A B : Ty} (d : ND (A :: Γ) B) : ND Γ (Ty.imp A B)
  | impE {Γ : List Ty} {A B : Ty} (d₁ : ND Γ (Ty.imp A B)) (d₂ : ND Γ A) :
      ND Γ B

/-- Simply typed lambda terms with named variables (names are
natural numbers; typing uses membership in the context). -/
inductive Tm : Type
  | var (x : ℕ) : Tm
  | lam (A : Ty) (t : Tm) : Tm
  | app (t u : Tm) : Tm

/-- Typing for STLC over a context assigning types to variable
names: a context is a list of `(name, type)` pairs; lookup is
by first match via `List.lookup`. To keep the correspondence
with `ND` elementary, contexts here are lists of types and a
variable is typed by membership of its type. -/
inductive HasType : List Ty → Tm → Ty → Prop
  | var {Γ : List Ty} {A : Ty} (x : ℕ) (h : A ∈ Γ) : HasType Γ (Tm.var x) A
  | lam {Γ : List Ty} {A B : Ty} {t : Tm}
      (d : HasType (A :: Γ) t B) : HasType Γ (Tm.lam A t) (Ty.imp A B)
  | app {Γ : List Ty} {A B : Ty} {t u : Tm}
      (d₁ : HasType Γ t (Ty.imp A B)) (d₂ : HasType Γ u A) :
      HasType Γ (Tm.app t u) B

/-- Curry-Howard, soundness direction: every typed term is a
natural-deduction proof of its type. -/
theorem curry_howard {Γ : List Ty} {t : Tm} {A : Ty}
    (d : HasType Γ t A) : ND Γ A := by
  induction d with
  | var x h => exact ND.hyp h
  | lam d ih => exact ND.impI ih
  | app d₁ d₂ ih₁ ih₂ => exact ND.impE ih₁ ih₂

end
