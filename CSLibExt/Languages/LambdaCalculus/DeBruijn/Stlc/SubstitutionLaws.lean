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
# Algebra of renamings and substitutions for STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Substitution

/-!
# Algebra of renamings and substitutions for STLC

This file develops the equational theory of the intrinsically typed de Bruijn
operations from `Substitution.lean`.  Substitutions form a category of typing
contexts, renamings embed into substitutions, and terms carry compatible
renaming and substitution actions.  The final section records naturality laws
for replacing the newest variable.

The organization follows the intrinsically typed treatment in the
[PLFA DeBruijn chapter](https://plfa.github.io/DeBruijn/).  In particular,
the proofs make the interaction between context extension and simultaneous
substitution explicit rather than relying on untyped index arithmetic.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Ξ Ω : List (Ty Base)}

namespace Sub

/-- Extend a substitution by an image for the newest variable. -/
def cons (a : Tm Δ A) (σ : Sub Γ Δ) : Sub (A :: Γ) Δ
  | _, .zero => a
  | _, .succ x => σ x

@[simp] theorem cons_zero (a : Tm Δ A) (σ : Sub Γ Δ) : cons a σ .zero = a := rfl

@[simp] theorem cons_succ (a : Tm Δ A) (σ : Sub Γ Δ) (x : Var Γ B) :
    cons a σ (.succ x) = σ x := rfl

/-- Compose simultaneous substitutions by substituting into every image. -/
def comp (σ : Sub Γ Δ) (τ : Sub Δ Ξ) : Sub Γ Ξ := fun x ↦ Tm.subst τ (σ x)

@[simp] theorem comp_apply (σ : Sub Γ Δ) (τ : Sub Δ Ξ) (x : Var Γ A) :
    comp σ τ x = Tm.subst τ (σ x) := rfl

@[simp] theorem cons_id_apply (a : Tm Γ A) (x : Var (A :: Γ) B) :
    cons a id x = single a x := by cases x <;> rfl

theorem lift_eq_cons_apply (σ : Sub Γ Δ) (x : Var (A :: Γ) B) :
    lift σ x = cons (.var .zero) (fun y ↦ Tm.weaken (σ y)) x := by cases x <;> rfl

end Sub

namespace Tm

/-! ## Fusion of renaming and substitution -/

/-- Renaming commutes with weakening under a correspondingly lifted renaming. -/
theorem rename_weaken (ρ : Ren Γ Δ) (t : Tm Γ A) :
    rename (Var.lift (A := B) ρ) (weaken (B := B) t) = weaken (B := B) (rename ρ t) := by
  rw [weaken, rename_comp, weaken, rename_comp]
  apply rename_congr
  intro C x
  rfl

/-- Renaming after substitution can be fused into the substitution images. -/
theorem rename_subst (ρ : Ren Δ Ξ) (σ : Sub Γ Δ) (t : Tm Γ A) :
    rename ρ (subst σ t) = subst (fun x ↦ rename ρ (σ x)) t := by
  induction t generalizing Δ Ξ with
  | var x => rfl
  | app f a ihf iha => simp [ihf, iha]
  | @lam A B Γ body ih =>
      simp only [subst_lam, rename_lam]
      rw [ih]
      congr 1
      apply subst_congr
      intro C x
      cases x with
      | zero => rfl
      | succ x => exact rename_weaken ρ (σ x)

/-- Substitution after renaming is substitution through the renamed variables. -/
theorem subst_rename (σ : Sub Δ Ξ) (ρ : Ren Γ Δ) (t : Tm Γ A) :
    subst σ (rename ρ t) = subst (fun x ↦ σ (ρ x)) t := by
  induction t generalizing Δ Ξ with
  | var x => rfl
  | app f a ihf iha => simp [ihf, iha]
  | @lam A B Γ body ih =>
      simp only [rename_lam, subst_lam]
      rw [ih]
      congr 1
      apply subst_congr
      intro C x
      cases x <;> rfl

/-- Substitution by a lifted environment commutes with weakening. -/
theorem subst_lift_weaken (σ : Sub Γ Δ) (t : Tm Γ A) :
    subst (Sub.lift (A := B) σ) (weaken (B := B) t) = weaken (B := B) (subst σ t) := by
  rw [weaken, subst_rename, weaken]
  rw [rename_subst]
  apply subst_congr
  intro C x
  rfl

/-- Two successive substitutions fuse into pointwise substitution of images. -/
theorem subst_subst (σ : Sub Γ Δ) (τ : Sub Δ Ξ) (t : Tm Γ A) :
    subst τ (subst σ t) = subst (Sub.comp σ τ) t := by
  induction t generalizing Δ Ξ with
  | var x => rfl
  | app f a ihf iha => simp [ihf, iha]
  | @lam A B Γ body ih =>
      simp only [subst_lam]
      rw [ih]
      congr 1
      apply subst_congr
      intro C x
      cases x with
      | zero => rfl
      | succ x => exact subst_lift_weaken τ (σ x)

end Tm

namespace Sub

/-! ## The category of typing contexts and substitutions -/

@[simp] theorem comp_id_apply (σ : Sub Γ Δ) (x : Var Γ A) :
    comp σ (id : Sub Δ Δ) x = σ x := Tm.subst_id (σ x)

@[simp] theorem id_comp_apply (σ : Sub Γ Δ) (x : Var Γ A) :
    comp (id : Sub Γ Γ) σ x = σ x := rfl

theorem comp_assoc_apply (σ : Sub Γ Δ) (τ : Sub Δ Ξ) (υ : Sub Ξ Ω) (x : Var Γ A) :
    comp (comp σ τ) υ x = comp σ (comp τ υ) x := Tm.subst_subst τ υ (σ x)

theorem comp_cons_apply (a : Tm Δ A) (σ : Sub Γ Δ) (τ : Sub Δ Ξ)
    (x : Var (A :: Γ) B) :
    comp (cons a σ) τ x = cons (Tm.subst τ a) (comp σ τ) x := by cases x <;> rfl

@[simp] theorem ofRen_id_apply (x : Var Γ A) : ofRen (Var.id : Ren Γ Γ) x = id x := rfl

theorem ofRen_comp_apply (ρ : Ren Γ Δ) (σ : Ren Δ Ξ) (x : Var Γ A) :
    ofRen (Var.comp ρ σ) x = comp (ofRen ρ) (ofRen σ) x := rfl

theorem ofRen_comp_sub_apply (ρ : Ren Γ Δ) (σ : Sub Δ Ξ) (x : Var Γ A) :
    comp (ofRen ρ) σ x = σ (ρ x) := rfl

theorem comp_ofRen_apply (σ : Sub Γ Δ) (ρ : Ren Δ Ξ) (x : Var Γ A) :
    comp σ (ofRen ρ) x = Tm.rename ρ (σ x) := Tm.subst_ofRen ρ (σ x)

theorem lift_id_apply (x : Var (A :: Γ) B) :
    lift (id : Sub Γ Γ) x = id x := by cases x <;> rfl

theorem lift_comp_apply (σ : Sub Γ Δ) (τ : Sub Δ Ξ) (x : Var (A :: Γ) B) :
    lift (comp σ τ) x = comp (lift σ) (lift τ) x := by
  cases x with
  | zero => rfl
  | succ x => exact (Tm.subst_lift_weaken τ (σ x)).symm

theorem lift_ofRen_apply (ρ : Ren Γ Δ) (x : Var (A :: Γ) B) :
    lift (ofRen ρ) x = ofRen (Var.lift ρ) x := by cases x <;> rfl

/-! ## Renaming substitution images -/

/-- Postcompose every image of a substitution with a renaming. -/
def rename (σ : Sub Γ Δ) (ρ : Ren Δ Ξ) : Sub Γ Ξ := fun x ↦ Tm.rename ρ (σ x)

@[simp] theorem rename_apply (σ : Sub Γ Δ) (ρ : Ren Δ Ξ) (x : Var Γ A) :
    rename σ ρ x = Tm.rename ρ (σ x) := rfl

@[simp] theorem rename_id_apply (σ : Sub Γ Δ) (x : Var Γ A) :
    rename σ Var.id x = σ x := Tm.rename_id (σ x)

theorem rename_comp_apply (σ : Sub Γ Δ) (ρ : Ren Δ Ξ) (τ : Ren Ξ Ω)
    (x : Var Γ A) :
    rename (rename σ ρ) τ x = rename σ (Var.comp ρ τ) x := Tm.rename_comp ρ τ (σ x)

theorem rename_cons_apply (a : Tm Δ A) (σ : Sub Γ Δ) (ρ : Ren Δ Ξ)
    (x : Var (A :: Γ) B) :
    rename (cons a σ) ρ x = cons (Tm.rename ρ a) (rename σ ρ) x := by cases x <;> rfl

theorem rename_eq_comp_ofRen_apply (σ : Sub Γ Δ) (ρ : Ren Δ Ξ) (x : Var Γ A) :
    rename σ ρ x = comp σ (ofRen ρ) x := (comp_ofRen_apply σ ρ x).symm

/-- Renaming lifted substitution images is compatible with lifting the renaming. -/
theorem rename_lift_apply (σ : Sub Γ Δ) (ρ : Ren Δ Ξ) (x : Var (A :: Γ) B) :
    rename (lift σ) (Var.lift ρ) x = lift (rename σ ρ) x := by
  cases x with
  | zero => rfl
  | succ x => exact Tm.rename_weaken ρ (σ x)

/-! ## Cancellation laws at a binder -/

/-- Composing a singleton substitution substitutes into its distinguished image. -/
theorem comp_single_apply (a : Tm Γ A) (σ : Sub Γ Δ) (x : Var (A :: Γ) B) :
    comp (single a) σ x = cons (Tm.subst σ a) σ x := by cases x <;> rfl

/-- Lifting and then replacing the new variable recovers context extension. -/
theorem lift_single_apply (σ : Sub Γ Δ) (a : Tm Δ A) (x : Var (A :: Γ) B) :
    comp (lift σ) (single a) x = cons a σ x := by
  cases x with
  | zero => rfl
  | succ x =>
      change Tm.subst (single a) (Tm.rename (fun y ↦ Var.succ y) (σ x)) = σ x
      rw [Tm.subst_rename]
      calc
        Tm.subst (fun y ↦ single a (.succ y)) (σ x) = Tm.subst id (σ x) := by
          apply Tm.subst_congr
          intro C y
          rfl
        _ = σ x := Tm.subst_id (σ x)

end Sub

namespace Tm

/-! ## Naturality of single substitution -/

/-- Substituting the newest variable after weakening recovers the original term. -/
@[simp] theorem subst_single_weaken (a : Tm Γ B) (t : Tm Γ A) :
    subst (Sub.single a) (weaken (B := B) t) = t := by
  rw [weaken, subst_rename]
  calc
    subst (fun x ↦ Sub.single a (.succ x)) t = subst Sub.id t := by
      apply subst_congr
      intro C x
      rfl
    _ = t := subst_id t

/-- Instantiating a weakened term has no effect. -/
@[simp] theorem instantiate_weaken (body : Tm Γ B) (a : Tm Γ A) :
    instantiate (weaken (B := A) body) a = body := subst_single_weaken a body

/-- Renaming commutes with replacement of the newest variable. -/
theorem rename_instantiate (ρ : Ren Γ Δ) (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    rename ρ (instantiate body a) =
      instantiate (rename (Var.lift ρ) body) (rename ρ a) := by
  rw [instantiate, rename_subst, instantiate, subst_rename]
  apply subst_congr
  intro C x
  cases x <;> rfl

/-- Simultaneous substitution commutes with replacement of the newest variable. -/
theorem subst_instantiate (σ : Sub Γ Δ) (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    subst σ (instantiate body a) =
      instantiate (subst (Sub.lift σ) body) (subst σ a) := by
  rw [instantiate, subst_subst, instantiate, subst_subst]
  apply subst_congr
  intro C x
  cases x with
  | zero => rfl
  | succ x => exact (subst_single_weaken (subst σ a) (σ x)).symm

/-- Extending an environment is equivalent to lifting it and then instantiating. -/
theorem subst_cons (σ : Sub Γ Δ) (body : Tm (A :: Γ) B) (a : Tm Δ A) :
    subst (Sub.cons a σ) body = instantiate (subst (Sub.lift σ) body) a := by
  rw [instantiate, subst_subst]
  apply subst_congr
  intro C x
  exact (Sub.lift_single_apply σ a x).symm

/-- The single-substitution operation is the special case of environment extension by identity. -/
theorem instantiate_eq_subst_cons (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    instantiate body a = subst (Sub.cons a Sub.id) body := by
  apply subst_congr
  intro C x
  cases x <;> rfl

end Tm

end Cslib.Languages.LambdaCalculus.Stlc
