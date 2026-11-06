/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.KindSemantics

/-! # Proved type-beta conversion for pure Fω

Conversion is the equivalence/congruence closure of type-operator beta,
not equality of semantic interpretations or an assumed conversion oracle.

The standard equational type theory is described by Robert Atkey,
*Relational Parametricity for Higher Kinds* (CSL 2012), Section 2, pp. 48-49,
https://doi.org/10.4230/LIPIcs.CSL.2012.46.
That formulation includes beta and eta; this project deliberately retains
only beta and its equivalence/congruence closure. It does not provide an
eta law, normalization theorem or decidable conversion procedure.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega.Ty

/-- **Type-beta conversion in Fω.** Type-beta conversion at a fixed context and kind. -/
inductive Conv : {Δ : List Kind} → {κ : Kind} → Ty Δ κ → Ty Δ κ → Prop where
  | refl {Δ : List Kind} {κ : Kind} (a : Ty Δ κ) : Conv a a
  | symm {Δ : List Kind} {κ : Kind} {a b : Ty Δ κ} :
      Conv a b → Conv b a
  | trans {Δ : List Kind} {κ : Kind} {a b c : Ty Δ κ} :
      Conv a b → Conv b c → Conv a c
  | beta {Δ : List Kind} {κ μ : Kind}
      (b : Ty (κ :: Δ) μ) (a : Ty Δ κ) :
      Conv (.app (.lam b) a) (instantiate b a)
  | lam {Δ : List Kind} {κ μ : Kind} {b c : Ty (κ :: Δ) μ} :
      Conv b c → Conv (.lam b) (.lam c)
  | app {Δ : List Kind} {κ μ : Kind}
      {f g : Ty Δ (.arrow κ μ)} {a b : Ty Δ κ} :
      Conv f g → Conv a b → Conv (.app f a) (.app g b)
  | arr {Δ : List Kind} {a a' b b' : Ty Δ .star} :
      Conv a a' → Conv b b' → Conv (.arr a b) (.arr a' b')
  | all {Δ : List Kind} {κ : Kind} {b c : Ty (κ :: Δ) .star} :
      Conv b c → Conv (.all b) (.all c)

variable {Δ Ε : List Kind} {κ μ : Kind} {a b : Ty Δ κ}

/-- **Soundness of type-beta conversion in kind algebras.**
Every type-beta conversion is sound in every semantic kind algebra. -/
theorem Conv.sound {α : Type*} (h : Conv a b) (M : KindAlgebra α)
    (η : KEnv α Δ) : eval M η a = eval M η b := by
  induction h with
  | refl => rfl
  | symm h ih => exact (ih η).symm
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ η).trans (ih₂ η)
  | beta body arg => exact (eval_instantiate M η body arg).symm
  | lam h ih =>
    funext x
    exact ih (KEnv.extend η x)
  | app h₁ h₂ ih₁ ih₂ =>
    simp only [eval]
    rw [ih₁ η, ih₂ η]
  | arr h₁ h₂ ih₁ ih₂ =>
    simp only [eval]
    rw [ih₁ η, ih₂ η]
  | all h ih =>
    simp only [eval]
    congr 1
    funext x
    exact ih (KEnv.extend η x)

/-- **Type-beta conversion is stable under renaming.**
Kind-preserving renaming respects proved type-beta conversion. -/
theorem Conv.rename (h : Conv a b) (ρ : KRen Δ Ε) :
    Conv (Ty.rename ρ a) (Ty.rename ρ b) := by
  induction h generalizing Ε with
  | refl => exact .refl _
  | symm h ih => exact (ih ρ).symm
  | trans h₁ h₂ ih₁ ih₂ => exact .trans (ih₁ ρ) (ih₂ ρ)
  | beta body arg =>
    rw [rename_instantiate]
    exact .beta (Ty.rename (KRen.lift ρ) body) (Ty.rename ρ arg)
  | lam h ih => exact .lam (ih (KRen.lift ρ))
  | app h₁ h₂ ih₁ ih₂ => exact .app (ih₁ ρ) (ih₂ ρ)
  | arr h₁ h₂ ih₁ ih₂ => exact .arr (ih₁ ρ) (ih₂ ρ)
  | all h ih => exact .all (ih (KRen.lift ρ))

/-- **Type-beta conversion is stable under substitution.**
Kind-preserving substitution respects proved type-beta conversion. -/
theorem Conv.subst (h : Conv a b) (σ : Sub Δ Ε) :
    Conv (Ty.subst σ a) (Ty.subst σ b) := by
  induction h generalizing Ε with
  | refl => exact .refl _
  | symm h ih => exact (ih σ).symm
  | trans h₁ h₂ ih₁ ih₂ => exact .trans (ih₁ σ) (ih₂ σ)
  | beta body arg =>
    rw [subst_instantiate]
    exact .beta (Ty.subst (liftSub σ) body) (Ty.subst σ arg)
  | lam h ih => exact .lam (ih (liftSub σ))
  | app h₁ h₂ ih₁ ih₂ => exact .app (ih₁ σ) (ih₂ σ)
  | arr h₁ h₂ ih₁ ih₂ => exact .arr (ih₁ σ) (ih₂ σ)
  | all h ih => exact .all (ih (liftSub σ))

/-- **Pointwise convertible substitutions give convertible results.**
Pointwise convertible substitution images give convertible results. -/
theorem Conv.subst_congr {σ τ : Sub Δ Ε}
    (h : ∀ {ν} (x : KVar Δ ν), Conv (σ x) (τ x)) (t : Ty Δ κ) :
    Conv (Ty.subst σ t) (Ty.subst τ t) := by
  induction t generalizing Ε with
  | var x => exact h x
  | app f a ihf iha => exact .app (ihf h) (iha h)
  | arr f a ihf iha => exact .arr (ihf h) (iha h)
  | lam b ih =>
    apply Conv.lam
    apply ih
    intro ν x
    cases x with
    | zero => exact .refl _
    | succ x => exact (h x).rename KVar.succ
  | all b ih =>
    apply Conv.all
    apply ih
    intro ν x
    cases x with
    | zero => exact .refl _
    | succ x => exact (h x).rename KVar.succ

private def kindDefault : (ν : Kind) → Kind.Sem Bool ν
  | .star => false
  | .arrow _ ν => fun _ => kindDefault ν

/-- **Function types are not convertible to quantified types.**
Term-function arrows cannot convert to quantified types, at any kind. -/
theorem not_conv_arr_all {a b : Ty Δ .star} {body : Ty (μ :: Δ) .star} :
    ¬ Conv (.arr a b) (.all body) := by
  intro h
  have e := h.sound
    (KindAlgebra.mk (fun _ _ => false) (fun {_} _ => true))
    (fun {ν} _ => kindDefault ν)
  exact Bool.noConfusion e

end Cslib.Languages.LambdaCalculus.FOmega.Ty
