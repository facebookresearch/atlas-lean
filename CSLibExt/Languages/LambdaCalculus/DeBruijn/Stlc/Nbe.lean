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
# Normalization by evaluation for STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Syntax

/-!
# Normalization by evaluation for STLC

This file builds the semantic foundation for normalization by evaluation in
the intrinsically typed simply typed lambda calculus.  Neutral and
beta-normal, eta-long terms are indexed by their contexts and types.  The
semantic domain is Kripke-style: semantic functions may be weakened to any
future context before being applied.  Reflection and reification connect
neutral syntax with this semantic domain.

The construction follows Ulrich Berger and Helmut Schwichtenberg,
[*An inverse of the evaluation functional for typed lambda-calculus*](https://doi.org/10.1109/LICS.1991.151645),
LICS 1991, pp. 203–211.  Its type-directed semantic evaluation and
reification architecture is adapted here to intrinsically typed de Bruijn
syntax; explicit future-context renamings provide the weakening needed during
reflection and reification.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Θ : List (Ty Base)}

mutual
  /-- Neutral terms are variables applied to zero or more normal arguments. -/
  inductive Ne {Base : Type u} : List (Ty Base) → Ty Base → Type u where
    | var {Γ : List (Ty Base)} {A : Ty Base} (x : Var (Base := Base) Γ A) :
        Ne (Base := Base) Γ A
    | app {Γ : List (Ty Base)} {A B : Ty Base}
        (f : Ne (Base := Base) Γ (A ⇒ B)) (a : Nf (Base := Base) Γ A) :
        Ne (Base := Base) Γ B

  /-- Beta-normal, eta-long terms.  At arrow type every normal form is a
  lambda; at base type it is neutral. -/
  inductive Nf {Base : Type u} : List (Ty Base) → Ty Base → Type u where
    | base {Γ : List (Ty Base)} {b : Base} (n : Ne (Base := Base) Γ (.base b)) :
        Nf (Base := Base) Γ (.base b)
    | lam {Γ : List (Ty Base)} {A B : Ty Base}
        (body : Nf (Base := Base) (A :: Γ) B) : Nf (Base := Base) Γ (A ⇒ B)
end

mutual
  /-- Rename the free variables of a neutral term. -/
  def Ne.rename : {Γ Δ : List (Ty Base)} → Ren Γ Δ → {A : Ty Base} → Ne Γ A → Ne Δ A
    | _, _, ρ, _, .var x => .var (ρ x)
    | _, _, ρ, _, .app f a => .app (Ne.rename ρ f) (Nf.rename ρ a)

  /-- Rename the free variables of a normal form. -/
  def Nf.rename : {Γ Δ : List (Ty Base)} → Ren Γ Δ → {A : Ty Base} → Nf Γ A → Nf Δ A
    | _, _, ρ, _, .base n => .base (Ne.rename ρ n)
    | _, _, ρ, _, .lam body => .lam (Nf.rename (Var.lift ρ) body)
end

@[simp] theorem Ne.rename_var (ρ : Ren Γ Δ) (x : Var Γ A) :
    (Ne.var x).rename ρ = .var (ρ x) := rfl

@[simp] theorem Ne.rename_app (ρ : Ren Γ Δ) (f : Ne Γ (A ⇒ B)) (a : Nf Γ A) :
    (Ne.app f a).rename ρ = .app (f.rename ρ) (a.rename ρ) := rfl

@[simp] theorem Nf.rename_base {b : Base} (ρ : Ren Γ Δ) (n : Ne Γ (.base b)) :
    (Nf.base n).rename ρ = .base (n.rename ρ) := rfl

@[simp] theorem Nf.rename_lam (ρ : Ren Γ Δ) (body : Nf (A :: Γ) B) :
    (Nf.lam body).rename ρ = .lam (body.rename (Var.lift ρ)) := rfl

theorem Ne.rename_congr {ρ σ : Ren Γ Δ}
    (h : ∀ {A} (x : Var Γ A), ρ x = σ x) (n : Ne Γ B) :
    n.rename ρ = n.rename σ := by
  exact Ne.rec
    (motive_1 := fun {Γ A} n => ∀ {Δ} (ρ σ : Ren Γ Δ),
      (∀ {C} (x : Var Γ C), ρ x = σ x) → n.rename ρ = n.rename σ)
    (motive_2 := fun {Γ A} n => ∀ {Δ} (ρ σ : Ren Γ Δ),
      (∀ {C} (x : Var Γ C), ρ x = σ x) → n.rename ρ = n.rename σ)
    (fun _ _ x {Δ} ρ σ h => by simp [h])
    (fun _ _ _ _ _ ihf iha {Δ} ρ σ h => by simp [ihf ρ σ h, iha ρ σ h])
    (fun _ _ _ ih {Δ} ρ σ h => by simp [ih ρ σ h])
    (fun _ _ _ _ ih {Δ} ρ σ h => by
      simp only [Nf.rename_lam]
      apply congrArg Nf.lam
      apply ih
      intro C x
      cases x with
      | zero => rfl
      | succ x => simp [h])
    n ρ σ h

theorem Nf.rename_congr {ρ σ : Ren Γ Δ}
    (h : ∀ {A} (x : Var Γ A), ρ x = σ x) (n : Nf Γ B) :
    n.rename ρ = n.rename σ := by
  exact Nf.rec
    (motive_1 := fun {Γ A} n => ∀ {Δ} (ρ σ : Ren Γ Δ),
      (∀ {C} (x : Var Γ C), ρ x = σ x) → n.rename ρ = n.rename σ)
    (motive_2 := fun {Γ A} n => ∀ {Δ} (ρ σ : Ren Γ Δ),
      (∀ {C} (x : Var Γ C), ρ x = σ x) → n.rename ρ = n.rename σ)
    (fun _ _ x {Δ} ρ σ h => by simp [h])
    (fun _ _ _ _ _ ihf iha {Δ} ρ σ h => by simp [ihf ρ σ h, iha ρ σ h])
    (fun _ _ _ ih {Δ} ρ σ h => by simp [ih ρ σ h])
    (fun _ _ _ _ ih {Δ} ρ σ h => by
      simp only [Nf.rename_lam]
      apply congrArg Nf.lam
      apply ih
      intro C x
      cases x with
      | zero => rfl
      | succ x => simp [h])
    n ρ σ h

@[simp] theorem Ne.rename_id (n : Ne Γ A) : n.rename Var.id = n := by
  exact Ne.rec
    (motive_1 := fun {_ _} n => n.rename Var.id = n)
    (motive_2 := fun {_ _} n => n.rename Var.id = n)
    (fun _ => rfl)
    (fun _ _ ihf iha => by simp [ihf, iha])
    (fun _ ih => by simp [ih])
    (fun body ih => by
      simp only [Nf.rename_lam]
      congr 1
      rw [Nf.rename_congr (fun x => Var.lift_id_apply x) body]
      exact ih)
    n

@[simp] theorem Nf.rename_id (n : Nf Γ A) : n.rename Var.id = n := by
  exact Nf.rec
    (motive_1 := fun {_ _} n => n.rename Var.id = n)
    (motive_2 := fun {_ _} n => n.rename Var.id = n)
    (fun _ => rfl)
    (fun _ _ ihf iha => by simp [ihf, iha])
    (fun _ ih => by simp [ih])
    (fun body ih => by
      simp only [Nf.rename_lam]
      congr 1
      rw [Nf.rename_congr (fun x => Var.lift_id_apply x) body]
      exact ih)
    n

theorem Ne.rename_comp (ρ : Ren Γ Δ) (σ : Ren Δ Θ) (n : Ne Γ A) :
    (n.rename ρ).rename σ = n.rename (Var.comp ρ σ) := by
  exact Ne.rec
    (motive_1 := fun {Γ A} n => ∀ {Δ Θ} (ρ : Ren Γ Δ) (σ : Ren Δ Θ),
      (n.rename ρ).rename σ = n.rename (Var.comp ρ σ))
    (motive_2 := fun {Γ A} n => ∀ {Δ Θ} (ρ : Ren Γ Δ) (σ : Ren Δ Θ),
      (n.rename ρ).rename σ = n.rename (Var.comp ρ σ))
    (fun _ _ _ {Δ Θ} ρ σ => rfl)
    (fun _ _ _ _ _ ihf iha {Δ Θ} ρ σ => by simp [ihf ρ σ, iha ρ σ])
    (fun _ _ _ ih {Δ Θ} ρ σ => by simp [ih ρ σ])
    (fun _ _ _ body ih {Δ Θ} ρ σ => by
      simp only [Nf.rename_lam]
      congr 1
      rw [ih (Var.lift ρ) (Var.lift σ)]
      apply Nf.rename_congr
      exact fun x => (Var.lift_comp_apply ρ σ x).symm)
    n ρ σ

theorem Nf.rename_comp (ρ : Ren Γ Δ) (σ : Ren Δ Θ) (n : Nf Γ A) :
    (n.rename ρ).rename σ = n.rename (Var.comp ρ σ) := by
  exact Nf.rec
    (motive_1 := fun {Γ A} n => ∀ {Δ Θ} (ρ : Ren Γ Δ) (σ : Ren Δ Θ),
      (n.rename ρ).rename σ = n.rename (Var.comp ρ σ))
    (motive_2 := fun {Γ A} n => ∀ {Δ Θ} (ρ : Ren Γ Δ) (σ : Ren Δ Θ),
      (n.rename ρ).rename σ = n.rename (Var.comp ρ σ))
    (fun _ _ _ {Δ Θ} ρ σ => rfl)
    (fun _ _ _ _ _ ihf iha {Δ Θ} ρ σ => by simp [ihf ρ σ, iha ρ σ])
    (fun _ _ _ ih {Δ Θ} ρ σ => by simp [ih ρ σ])
    (fun _ _ _ body ih {Δ Θ} ρ σ => by
      simp only [Nf.rename_lam]
      congr 1
      rw [ih (Var.lift ρ) (Var.lift σ)]
      apply Nf.rename_congr
      exact fun x => (Var.lift_comp_apply ρ σ x).symm)
    n ρ σ

mutual
  /-- Forget the neutral-term invariant. -/
  def Ne.toTm : {Γ : List (Ty Base)} → {A : Ty Base} → Ne Γ A → Tm Γ A
    | _, _, .var x => .var x
    | _, _, .app f a => .app f.toTm a.toTm

  /-- Forget the normal-form invariant. -/
  def Nf.toTm : {Γ : List (Ty Base)} → {A : Ty Base} → Nf Γ A → Tm Γ A
    | _, _, .base n => n.toTm
    | _, _, .lam body => .lam body.toTm
end

@[simp] theorem Ne.toTm_var (x : Var Γ A) : (Ne.var x).toTm = .var x := rfl

@[simp] theorem Ne.toTm_app (f : Ne Γ (A ⇒ B)) (a : Nf Γ A) :
    (Ne.app f a).toTm = .app f.toTm a.toTm := rfl

@[simp] theorem Nf.toTm_base {b : Base} (n : Ne Γ (.base b)) :
    (Nf.base n).toTm = n.toTm := rfl

@[simp] theorem Nf.toTm_lam (body : Nf (A :: Γ) B) :
    (Nf.lam body).toTm = .lam body.toTm := rfl

theorem Ne.toTm_rename (ρ : Ren Γ Δ) (n : Ne Γ A) :
    (n.rename ρ).toTm = Tm.rename ρ n.toTm := by
  exact Ne.rec
    (motive_1 := fun {Γ A} n => ∀ {Δ} (ρ : Ren Γ Δ),
      (n.rename ρ).toTm = Tm.rename ρ n.toTm)
    (motive_2 := fun {Γ A} n => ∀ {Δ} (ρ : Ren Γ Δ),
      (n.rename ρ).toTm = Tm.rename ρ n.toTm)
    (fun _ _ _ {Δ} ρ => rfl)
    (fun _ _ _ _ _ ihf iha {Δ} ρ => by simp [ihf ρ, iha ρ])
    (fun _ _ _ ih {Δ} ρ => by simp [ih ρ])
    (fun _ _ _ _ ih {Δ} ρ => by simp [ih (Var.lift ρ)])
    n ρ

theorem Nf.toTm_rename (ρ : Ren Γ Δ) (n : Nf Γ A) :
    (n.rename ρ).toTm = Tm.rename ρ n.toTm := by
  exact Nf.rec
    (motive_1 := fun {Γ A} n => ∀ {Δ} (ρ : Ren Γ Δ),
      (n.rename ρ).toTm = Tm.rename ρ n.toTm)
    (motive_2 := fun {Γ A} n => ∀ {Δ} (ρ : Ren Γ Δ),
      (n.rename ρ).toTm = Tm.rename ρ n.toTm)
    (fun _ _ _ {Δ} ρ => rfl)
    (fun _ _ _ _ _ ihf iha {Δ} ρ => by simp [ihf ρ, iha ρ])
    (fun _ _ _ ih {Δ} ρ => by simp [ih ρ])
    (fun _ _ _ _ ih {Δ} ρ => by simp [ih (Var.lift ρ)])
    n ρ

/-- **Kripke semantic values.** For a context $\Gamma$, the semantic values of a simple type in
$\Gamma$ are defined by recursion on the type. At a base type $b$ they are the neutral terms of
type $b$ in $\Gamma$ (variables applied to zero or more normal arguments). At an arrow type
$A \Rightarrow B$ a semantic value is a family that, for every context $\Delta$ and every
renaming from $\Gamma$ to $\Delta$, maps semantic values of type $A$ in $\Delta$ to semantic
values of type $B$ in $\Delta$.

Because a semantic function acts after every renaming into a later context, reification under a
binder needs no untyped weakening operation. -/
def Sem (Γ : List (Ty Base)) : Ty Base → Type u
  | .base b => Ne Γ (.base b)
  | A ⇒ B => ∀ {Δ}, Ren Γ Δ → Sem Δ A → Sem Δ B

namespace Sem

/-- **Renaming a semantic value.** Given a renaming $\rho$ from a context $\Gamma$ to a context
$\Delta$, a simple type $A$ and a semantic value $v$ of type $A$ in $\Gamma$, the renamed value is
the semantic value of type $A$ in $\Delta$ defined by cases on $A$. At a base type it is the
neutral term $v$ with its free variables renamed by $\rho$. At an arrow type
$A = B \Rightarrow C$ it sends a renaming $\sigma$ from $\Delta$ to a context $\Theta$ and a
semantic value $a$ of type $B$ in $\Theta$ to the semantic value of type $C$ in $\Theta$ that $v$
assigns to the composite renaming ($\rho$ followed by $\sigma$) and $a$. -/
def rename (ρ : Ren Γ Δ) (A : Ty Base) (v : Sem Γ A) : Sem Δ A :=
  match A with
  | .base _ => Ne.rename ρ v
  | _ ⇒ _ => fun σ a => v (Var.comp ρ σ) a

@[simp] theorem rename_base {b : Base} (ρ : Ren Γ Δ) (n : Sem Γ (.base b)) :
    rename ρ (.base b) n = n.rename ρ := rfl

@[simp] theorem rename_arr_apply (ρ : Ren Γ Δ) (f : Sem Γ (A ⇒ B))
    (σ : Ren Δ Θ) (a : Sem Θ A) :
    rename ρ (A ⇒ B) f σ a = f (Var.comp ρ σ) a := rfl

@[simp] theorem rename_id (A : Ty Base) (v : Sem Γ A) :
    rename Var.id A v = v := by
  cases A with
  | base => exact Ne.rename_id v
  | arr => rfl

theorem rename_comp (ρ : Ren Γ Δ) (σ : Ren Δ Θ) (A : Ty Base) (v : Sem Γ A) :
    rename σ A (rename ρ A v) = rename (Var.comp ρ σ) A v := by
  cases A with
  | base => exact Ne.rename_comp ρ σ v
  | arr => rfl

end Sem

mutual
  /-- Reflect a neutral term into the semantic domain. -/
  def reflect : (A : Ty Base) → {Γ : List (Ty Base)} → Ne Γ A → Sem Γ A
    | .base _, _, n => n
    | A ⇒ B, _, n => fun ρ a => reflect B (.app (n.rename ρ) (quote A a))

  /-- Reify a semantic value as a beta-normal, eta-long term. -/
  def quote : (A : Ty Base) → {Γ : List (Ty Base)} → Sem Γ A → Nf Γ A
    | .base _, _, v => .base v
    | A ⇒ B, _, v => .lam (quote B (v .succ (reflect A (.var .zero))))
end

/-- **Semantic environments for normalization by evaluation.** For contexts $\Delta$ and
$\Gamma$, a semantic environment for $\Gamma$ in $\Delta$ assigns to every variable of $\Gamma$,
of any type $A$, a Kripke semantic value of type $A$ in $\Delta$. -/
abbrev SemEnv (Δ Γ : List (Ty Base)) := ∀ {A}, Var Γ A → Sem Δ A

namespace SemEnv

/-- **Renaming a semantic environment.** Given a renaming $\rho$ from a context $\Delta$ to a
context $\Theta$ and a semantic environment $\eta$ for $\Gamma$ in $\Delta$, the renamed
environment is the semantic environment for $\Gamma$ in $\Theta$ that sends each variable $x$ of
type $A$ to the semantic value $\eta(x)$ renamed along $\rho$ at type $A$. -/
def rename (ρ : Ren Δ Θ) (η : SemEnv Δ Γ) : SemEnv Θ Γ :=
  fun {A} x => Sem.rename ρ A (η x)

@[simp] theorem rename_apply (ρ : Ren Δ Θ) (η : SemEnv Δ Γ) (x : Var Γ A) :
    rename ρ η x = Sem.rename ρ A (η x) := rfl

@[simp] theorem rename_id (η : SemEnv Δ Γ) :
    @rename Base Γ Δ Δ Var.id η = @η := by
  funext A x
  exact Sem.rename_id A (η x)

theorem rename_comp {Ω : List (Ty Base)} (ρ : Ren Δ Θ) (σ : Ren Θ Ω)
    (η : SemEnv Δ Γ) :
    @rename Base Γ Θ Ω σ (@rename Base Γ Δ Θ ρ η) =
      @rename Base Γ Δ Ω (Var.comp ρ σ) η := by
  funext A x
  exact Sem.rename_comp ρ σ A (η x)

/-- **Extending a semantic environment by one variable.** Given a semantic value $a$ of type $A$
in a context $\Delta$ and a semantic environment $\eta$ for $\Gamma$ in $\Delta$, the extended
environment is the semantic environment for the context $A :: \Gamma$ (the context $\Gamma$ with a
new innermost variable of type $A$) in $\Delta$ that sends the new innermost variable to $a$ and
sends the successor of each variable $x$ of $\Gamma$ to $\eta(x)$. -/
def cons (a : Sem Δ A) (η : SemEnv Δ Γ) : SemEnv Δ (A :: Γ)
  | _, .zero => a
  | _, .succ x => η x

@[simp] theorem cons_zero (a : Sem Δ A) (η : SemEnv Δ Γ) :
    cons a η (.zero : Var (A :: Γ) A) = a := rfl

@[simp] theorem cons_succ (a : Sem Δ A) (η : SemEnv Δ Γ) (x : Var Γ B) :
    cons a η (.succ x) = η x := rfl

/-- **The identity semantic environment.** For a context $\Gamma$, the identity environment is the
semantic environment for $\Gamma$ in $\Gamma$ that sends each variable $x$ of type $A$ to the
reflection at type $A$ of the neutral term $x$. Reflection turns a neutral term into a semantic
value of the same type in the same context. -/
def identity : SemEnv Γ Γ := fun {A} x => reflect A (.var x)

end SemEnv

end Cslib.Languages.LambdaCalculus.Stlc
