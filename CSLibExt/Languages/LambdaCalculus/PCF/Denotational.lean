/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PCF: denotational semantics over ω-complete partial orders
-/
module

public import CSLibExt.Languages.LambdaCalculus.PCF.Syntax
public import MathlibExt.Order.OmegaCompletePartialOrder.ContinuousHom
public import Mathlib.Order.Category.OmegaCompletePartialOrder

/-!
# Denotational semantics of PCF

The standard Scott-domain model of PCF (Plotkin 1977; Streicher 2006), built on
Mathlib's ω-complete partial orders and the continuous-map API of
`MathlibExt.Order.OmegaCompletePartialOrder.ContinuousHom` (`⊥` for function
spaces, `ContinuousHom.curry`, Kleene least fixed points `ContinuousHom.lfp`):

* `Ty.dom`: the ground type denotes the flat domain `Part ℕ`; `A → B` denotes
  the continuous function space `dom A →𝒄 dom B`. Every domain is pointed
  (`OrderBot`).
* `Env Γ`: environments are nested products, `Env (A :: Γ) = Env Γ × dom A`.
* `Tm.denote t : Env Γ →𝒄 dom A`: variables are projections, abstraction is
  currying, application is pointwise application, `succ`/`pred` are strict maps
  on `Part ℕ` (`ContinuousHom.map`), `ifz` is the strict zero test (`ifzHom`),
  and `fix t` is the least fixed point of the denotation of `t`.

The constructor equations `denote_var`, …, `denote_fix` hold by `rfl` and are
meant for `rw`/`change`: the domains are bundled `ωCPO` objects computed by
recursion on types, which keeps `simp`'s indexing from matching them. The
renaming and substitution lemmas (`denote_rename`, `denote_weaken`,
`denote_subst`, `denote_instantiate`) relate syntactic substitution to
environment update; `denote_fix_unfold` is the fixed-point equation.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.PCF

open scoped CslibStlc
open OmegaCompletePartialOrder

/-- The domain denoted by a PCF type. -/
@[reducible] noncomputable def Ty.dom : Ty → ωCPO.{0}
  | .base _ => ωCPO.of (Part ℕ)
  | .arr A B => ωCPO.of (Ty.dom A →𝒄 Ty.dom B)

/-- Every domain of a PCF type has a least element. -/
@[instance_reducible] noncomputable def Ty.orderBot : (A : Ty) → OrderBot (Ty.dom A)
  | .base _ => inferInstanceAs (OrderBot (Part ℕ))
  | .arr A B => @ContinuousHom.instOrderBot (Ty.dom A) (Ty.dom B) _ _ (Ty.orderBot B)

noncomputable instance (A : Ty) : OrderBot (Ty.dom A) := Ty.orderBot A

/-- The semantic environment for a context. -/
@[reducible] noncomputable def Env : List Ty → ωCPO.{0}
  | [] => ωCPO.of PUnit
  | A :: Γ => ωCPO.of (Env Γ × Ty.dom A)

variable {Γ Δ : List Ty} {A B : Ty}

/-- Variable lookup in an environment, as a continuous map. -/
noncomputable def Env.lookup : {Γ : List Ty} → {A : Ty} → Var Γ A → (Env Γ →𝒄 Ty.dom A)
  | _ :: _, _, .zero => ContinuousHom.ofFun Prod.snd
  | _ :: _, _, .succ x => (Env.lookup x).comp (ContinuousHom.ofFun Prod.fst)

/-- The environment with the given value at every variable. -/
noncomputable def Env.ofFun : {Γ : List Ty} → (∀ {A}, Var Γ A → Ty.dom A) → Env Γ
  | [], _ => PUnit.unit
  | _ :: _, f => (Env.ofFun fun x => f (.succ x), f .zero)

theorem Env.lookup_zero (η : Env Γ) (a : Ty.dom A) :
    Env.lookup (.zero : Var (A :: Γ) A) ((η, a) : Env (A :: Γ)) = a := rfl

theorem Env.lookup_succ (η : Env Γ) (a : Ty.dom B) (x : Var Γ A) :
    Env.lookup (.succ x : Var (B :: Γ) A) ((η, a) : Env (B :: Γ)) = Env.lookup x η := rfl

theorem Env.lookup_ofFun (f : ∀ {A}, Var Γ A → Ty.dom A) (x : Var Γ A) :
    Env.lookup x (Env.ofFun f) = f x := by
  induction x with
  | zero => rfl
  | succ x ih => exact ih (fun y => f (.succ y))

theorem Env.ofFun_congr {f g : ∀ {A}, Var Γ A → Ty.dom A}
    (h : ∀ {A} (x : Var Γ A), f x = g x) : Env.ofFun f = Env.ofFun g := by
  induction Γ with
  | nil => rfl
  | cons C Γ ih =>
      change (Env.ofFun fun x => f (.succ x), f .zero) = (Env.ofFun fun x => g (.succ x), g .zero)
      rw [ih (fun x => h (.succ x)), h .zero]

theorem Env.ofFun_lookup (η : Env Γ) : Env.ofFun (fun x => Env.lookup x η) = η := by
  induction Γ with
  | nil => rfl
  | cons C Γ ih =>
      obtain ⟨η, a⟩ := η
      change (Env.ofFun fun x => Env.lookup x η, a) = (η, a)
      rw [ih]

/-- The strict zero test on `Part ℕ`, pointwise in an environment: `s₁` if the
test is `0`, `s₂` if it is a successor, undefined if it is undefined. -/
noncomputable def ifzHom {α : Type*} [OmegaCompletePartialOrder α] (t s₁ s₂ : α →𝒄 Part ℕ) :
    α →𝒄 Part ℕ :=
  ContinuousHom.ofFun (fun x => (t x).bind fun n => if n = 0 then s₁ x else s₂ x)
    (ContinuousHom.ωScottContinuous.bind t.ωScottContinuous (by
      refine ωScottContinuous.of_apply₂ fun n => ?_
      by_cases hn : n = 0
      · simpa [hn] using s₁.ωScottContinuous
      · simpa [hn] using s₂.ωScottContinuous))

namespace Tm

/-- The denotation of a term: a continuous map from environments to the domain
of its type. -/
noncomputable def denote : {Γ : List Ty} → {A : Ty} → Tm Γ A → (Env Γ →𝒄 Ty.dom A)
  | _, _, .var x => Env.lookup x
  | _, _, .lam body => ContinuousHom.curry (denote body)
  | _, _, .app f a => ContinuousHom.ofFun (fun η => denote f η (denote a η))
      (ContinuousHom.ωScottContinuous_apply (denote f).ωScottContinuous
        (denote a).ωScottContinuous)
  | _, _, .zero => ContinuousHom.const (Part.some 0)
  | _, _, .succ t => ContinuousHom.map Nat.succ (denote t)
  | _, _, .pred t => ContinuousHom.map Nat.pred (denote t)
  | _, _, .ifz t s₁ s₂ => ifzHom (denote t) (denote s₁) (denote s₂)
  | _, _, .fix t => ContinuousHom.lfpHom.comp (denote t)

section Equations

variable (η : Env Γ)

theorem denote_var (x : Var Γ A) : denote (.var x) η = Env.lookup x η := rfl
theorem denote_lam (body : Tm (A :: Γ) B) (a : Ty.dom A) :
    denote (.lam body) η a = denote body ((η, a) : Env (A :: Γ)) := rfl
theorem denote_app (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) :
    denote (.app f a) η = denote f η (denote a η) := rfl
theorem denote_zero : denote (.zero : Tm Γ .nat) η = Part.some 0 := rfl
theorem denote_succ (t : Tm Γ .nat) :
    denote (.succ t) η = (denote t η : Part ℕ).map Nat.succ := rfl
theorem denote_pred (t : Tm Γ .nat) :
    denote (.pred t) η = (denote t η : Part ℕ).map Nat.pred := rfl
theorem denote_ifz (t s₁ s₂ : Tm Γ .nat) :
    denote (.ifz t s₁ s₂) η =
      (denote t η : Part ℕ).bind fun n => if n = 0 then denote s₁ η else denote s₂ η := rfl
theorem denote_fix (t : Tm Γ (A ⇒ A)) : denote (.fix t) η = ContinuousHom.lfp (denote t η) :=
  rfl

/-- The fixed-point equation: `fix t` denotes the same as `t (fix t)`. -/
theorem denote_fix_unfold (t : Tm Γ (A ⇒ A)) :
    denote (.fix t) η = denote (.app t (.fix t)) η :=
  (ContinuousHom.lfp_eq (denote t η)).symm

theorem denote_numeral (n : Nat) : denote (numeral n : Tm Γ .nat) η = Part.some n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (denote (numeral n) η : Part ℕ).map Nat.succ = Part.some (n + 1)
      rw [ih, Part.map_some]

end Equations

/-- Denotation commutes with renaming. -/
theorem denote_rename (ρ : Ren Γ Δ) (t : Tm Γ A) (η : Env Δ) :
    denote (rename ρ t) η = denote t (Env.ofFun fun x => Env.lookup (ρ x) η) := by
  induction t generalizing Δ with
  | var x => exact (Env.lookup_ofFun (fun y => Env.lookup (ρ y) η) x).symm
  | @lam Γ A B body ih =>
      refine ContinuousHom.ext _ _ fun a => ?_
      change denote (rename (Stlc.Var.lift ρ) body) ((η, a) : Env (A :: Δ)) =
        denote body ((Env.ofFun fun x => Env.lookup (ρ x) η, a) : Env (A :: Γ))
      rw [ih]
      rfl
  | app f a ihf iha => rw [rename_app, denote_app, denote_app, ihf, iha]
  | zero => rfl
  | succ t ih => rw [rename_succ, denote_succ, denote_succ, ih]
  | pred t ih => rw [rename_pred, denote_pred, denote_pred, ih]
  | ifz t s₁ s₂ iht ih₁ ih₂ => rw [rename_ifz, denote_ifz, denote_ifz, iht, ih₁, ih₂]
  | fix t ih => rw [rename_fix, denote_fix, denote_fix, ih]

/-- Weakening does not change the denotation. -/
theorem denote_weaken (t : Tm Γ A) (η : Env Γ) (b : Ty.dom B) :
    denote (weaken (B := B) t) ((η, b) : Env (B :: Γ)) = denote t η := by
  rw [weaken, denote_rename]
  congr 1
  exact (Env.ofFun_congr fun _ => rfl).trans (Env.ofFun_lookup η)

/-- Denotation commutes with substitution. -/
theorem denote_subst (σ : Sub Γ Δ) (t : Tm Γ A) (η : Env Δ) :
    denote (subst σ t) η = denote t (Env.ofFun fun x => denote (σ x) η) := by
  induction t generalizing Δ with
  | var x => exact (Env.lookup_ofFun (fun y => denote (σ y) η) x).symm
  | @lam Γ A B body ih =>
      refine ContinuousHom.ext _ _ fun a => ?_
      change denote (subst (Sub.lift σ) body) ((η, a) : Env (A :: Δ)) =
        denote body ((Env.ofFun fun x => denote (σ x) η, a) : Env (A :: Γ))
      rw [ih]
      refine congrArg (denote body) (Prod.ext ?_ rfl)
      exact Env.ofFun_congr fun {C} (x : Var Γ C) => denote_weaken (σ x) η a
  | app f a ihf iha => rw [subst_app, denote_app, denote_app, ihf, iha]
  | zero => rfl
  | succ t ih => rw [subst_succ, denote_succ, denote_succ, ih]
  | pred t ih => rw [subst_pred, denote_pred, denote_pred, ih]
  | ifz t s₁ s₂ iht ih₁ ih₂ => rw [subst_ifz, denote_ifz, denote_ifz, iht, ih₁, ih₂]
  | fix t ih => rw [subst_fix, denote_fix, denote_fix, ih]

/-- Substituting for the newest variable is environment extension. -/
theorem denote_instantiate (body : Tm (A :: Γ) B) (a : Tm Γ A) (η : Env Γ) :
    denote (body.instantiate a) η = denote body ((η, denote a η) : Env (A :: Γ)) := by
  rw [instantiate, denote_subst]
  congr 1
  refine Prod.ext ?_ rfl
  exact (Env.ofFun_congr fun _ => rfl).trans (Env.ofFun_lookup η)

end Tm

end Cslib.Languages.LambdaCalculus.PCF
