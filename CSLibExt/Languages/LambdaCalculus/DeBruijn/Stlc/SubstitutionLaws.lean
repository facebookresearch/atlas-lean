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

/-- **Extension of a simply typed substitution.** Given a term $a$ of type $A$ in a context
$\Delta$ and a substitution $\sigma$ from $\Gamma$ to $\Delta$, the extension of $\sigma$ by $a$ is
the substitution from the context $\Gamma$ extended by a newest variable of type $A$ to $\Delta$
that sends the newest variable to $a$ and each older variable $x$ of $\Gamma$ to $\sigma(x)$. -/
def cons (a : Tm Δ A) (σ : Sub Γ Δ) : Sub (A :: Γ) Δ
  | _, .zero => a
  | _, .succ x => σ x

@[simp] theorem cons_zero (a : Tm Δ A) (σ : Sub Γ Δ) : cons a σ .zero = a := rfl

@[simp] theorem cons_succ (a : Tm Δ A) (σ : Sub Γ Δ) (x : Var Γ B) :
    cons a σ (.succ x) = σ x := rfl

/-- **Composition of simply typed substitutions.** For substitutions $\sigma$ from a context
$\Gamma$ to $\Delta$ and $\tau$ from $\Delta$ to $\Xi$, the composite of $\sigma$ followed by
$\tau$ is the substitution from $\Gamma$ to $\Xi$ that sends each variable $x$ of $\Gamma$ to the
term obtained by applying $\tau$ to $\sigma(x)$. -/
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

/-- **Renaming commutes with weakening for intrinsically typed STLC terms.** Let $\rho$ be a
renaming from the typing context $\Gamma$ to the typing context $\Delta$, $t$ a term of type $A$
in context $\Gamma$, and $B$ a type. Weakening $t$ by a new newest variable of type $B$ and then
renaming by the lift of $\rho$ under that variable gives the same term as renaming $t$ by $\rho$
and then weakening by a new newest variable of type $B$. -/
theorem rename_weaken (ρ : Ren Γ Δ) (t : Tm Γ A) :
    rename (Var.lift (A := B) ρ) (weaken (B := B) t) = weaken (B := B) (rename ρ t) := by
  rw [weaken, rename_comp, weaken, rename_comp]
  apply rename_congr
  intro C x
  rfl

/-- **Renaming after substitution in the simply typed calculus.** Let $\sigma$ be a substitution
from $\Gamma$ to $\Delta$, $\rho$ a renaming from $\Delta$ to $\Xi$ and $t$ a term of type $A$ in
$\Gamma$. Renaming by $\rho$ the result of applying $\sigma$ to $t$ gives the result of applying
to $t$ the substitution that sends each variable $x$ of $\Gamma$ to $\sigma(x)$ renamed by
$\rho$. -/
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

/-- **Renaming then substituting an intrinsically typed STLC term.** Let $\rho$ be a renaming from
the typing context $\Gamma$ to the typing context $\Delta$, $\sigma$ a substitution from $\Delta$
to the typing context $\Xi$, and $t$ a term of type $A$ in context $\Gamma$. Renaming $t$ by
$\rho$ and then applying $\sigma$ gives the same term as applying to $t$ the substitution that
sends each variable $x$ of $\Gamma$ to $\sigma(\rho(x))$. -/
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

/-- **Lifted substitution commutes with weakening for intrinsically typed STLC terms.** Let
$\sigma$ be a substitution from the typing context $\Gamma$ to the typing context $\Delta$, $t$ a
term of type $A$ in context $\Gamma$, and $B$ a type. Weakening $t$ by a new newest variable of
type $B$ and then applying the lift of $\sigma$ under that variable gives the same term as
applying $\sigma$ to $t$ and then weakening by a new newest variable of type $B$. -/
theorem subst_lift_weaken (σ : Sub Γ Δ) (t : Tm Γ A) :
    subst (Sub.lift (A := B) σ) (weaken (B := B) t) = weaken (B := B) (subst σ t) := by
  rw [weaken, subst_rename, weaken]
  rw [rename_subst]
  apply subst_congr
  intro C x
  rfl

/-- **Composition of substitutions for intrinsically typed STLC terms.** Let $\sigma$ be a
substitution from the typing context $\Gamma$ to the typing context $\Delta$, $\tau$ a
substitution from $\Delta$ to the typing context $\Xi$, and $t$ a term of type $A$ in context
$\Gamma$. Applying $\sigma$ to $t$ and then applying $\tau$ gives the same term as applying to $t$
the composite substitution, which sends each variable $x$ of $\Gamma$ to the result of applying
$\tau$ to $\sigma(x)$. -/
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

/-- **Right identity law for composition of substitutions.** For every simultaneous substitution
$\sigma$ from a context $\Gamma$ to a context $\Delta$ and every variable $x$ of type $A$ in
$\Gamma$, the composite of $\sigma$ followed by the identity substitution on $\Delta$ sends $x$ to
$\sigma(x)$. -/
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

/-- **Renaming the images of a substitution.** Given a substitution $\sigma$ from the typing
context $\Gamma$ to the typing context $\Delta$ and a renaming $\rho$ from $\Delta$ to the typing
context $\Xi$, the substitution from $\Gamma$ to $\Xi$ obtained by renaming images sends each
variable $x$ of $\Gamma$ to the renaming of the term $\sigma(x)$ by $\rho$. -/
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

/-- **Lifting commutes with renaming substitution images.** Let $\sigma$ be a substitution from
$\Gamma$ to $\Delta$ and $\rho$ a renaming from $\Delta$ to $\Xi$. Lift $\sigma$ under a binder
of type $A$ and rename each of its images by the lift of $\rho$ under the same binder. At every
variable $x$ of the context $\Gamma$ extended by a newest variable of type $A$, this gives the
same term as the lift under that binder of the substitution that renames each image of $\sigma$
by $\rho$. -/
theorem rename_lift_apply (σ : Sub Γ Δ) (ρ : Ren Δ Ξ) (x : Var (A :: Γ) B) :
    rename (lift σ) (Var.lift ρ) x = lift (rename σ ρ) x := by
  cases x with
  | zero => rfl
  | succ x => exact Tm.rename_weaken ρ (σ x)

/-! ## Cancellation laws at a binder -/

/-- **Composing a single substitution with a substitution.** Let $a$ be a term of type $A$ in a
context $\Gamma$ and $\sigma$ a substitution from $\Gamma$ to $\Delta$, and write $a[\sigma]$ for
the result of applying $\sigma$ to $a$. The composite of the single substitution of $a$ for the
newest variable followed by $\sigma$ agrees, at every variable $x$ of the context $\Gamma$
extended by a newest variable of type $A$, with the extension of $\sigma$ that sends the newest
variable to $a[\sigma]$. -/
theorem comp_single_apply (a : Tm Γ A) (σ : Sub Γ Δ) (x : Var (A :: Γ) B) :
    comp (single a) σ x = cons (Tm.subst σ a) σ x := by cases x <;> rfl

/-- **Lifting followed by single substitution.** Let $\sigma$ be a substitution from $\Gamma$ to
$\Delta$ and $a$ a term of type $A$ in $\Delta$. The composite of the lift of $\sigma$ under a
binder of type $A$ followed by the single substitution of $a$ for the newest variable agrees, at
every variable $x$ of the context $\Gamma$ extended by a newest variable of type $A$, with the
extension of $\sigma$ that sends the newest variable to $a$ and each older variable $y$ to
$\sigma(y)$. -/
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

/-- **Single substitution cancels weakening.** Let $t$ be a term of type $A$ in the typing context
$\Gamma$ and $a$ a term of type $B$ in context $\Gamma$. Weakening $t$ by a new newest variable of
type $B$ and then applying the substitution that replaces the newest variable by $a$ and leaves
every older variable unchanged gives back $t$. -/
@[simp] theorem subst_single_weaken (a : Tm Γ B) (t : Tm Γ A) :
    subst (Sub.single a) (weaken (B := B) t) = t := by
  rw [weaken, subst_rename]
  calc
    subst (fun x ↦ Sub.single a (.succ x)) t = subst Sub.id t := by
      apply subst_congr
      intro C x
      rfl
    _ = t := subst_id t

/-- **Instantiating a weakened term.** For terms $b$ of type $B$ and $a$ of type $A$ in a context
$\Gamma$, weakening $b$ to the context $\Gamma$ extended by a newest variable of type $A$ and then
instantiating that newest variable by $a$ gives back $b$. -/
@[simp] theorem instantiate_weaken (body : Tm Γ B) (a : Tm Γ A) :
    instantiate (weaken (B := A) body) a = body := subst_single_weaken a body

/-- **Renaming commutes with instantiation.** Let $\rho$ be a renaming from $\Gamma$ to $\Delta$,
$b$ a term of type $B$ in the context $\Gamma$ extended by a newest variable of type $A$, and $a$
a term of type $A$ in $\Gamma$. Renaming by $\rho$ the instantiation of the newest variable of $b$
by $a$ gives the instantiation of the newest variable of $b'$ by $a'$, where $b'$ is $b$ renamed
by the lift of $\rho$ under the binder and $a'$ is $a$ renamed by $\rho$. -/
theorem rename_instantiate (ρ : Ren Γ Δ) (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    rename ρ (instantiate body a) =
      instantiate (rename (Var.lift ρ) body) (rename ρ a) := by
  rw [instantiate, rename_subst, instantiate, subst_rename]
  apply subst_congr
  intro C x
  cases x <;> rfl

/-- **Substitution commutes with instantiation for intrinsically typed STLC terms.** Let $\sigma$
be a substitution from the typing context $\Gamma$ to the typing context $\Delta$, $s$ a term of
type $B$ in the context $\Gamma$ extended by a newest variable of type $A$, and $a$ a term of type
$A$ in context $\Gamma$. Replacing the newest variable of $s$ by $a$ and then applying $\sigma$
gives the same term as applying the lift of $\sigma$ to $s$ and then replacing the newest variable
of the result by the term obtained by applying $\sigma$ to $a$. -/
theorem subst_instantiate (σ : Sub Γ Δ) (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    subst σ (instantiate body a) =
      instantiate (subst (Sub.lift σ) body) (subst σ a) := by
  rw [instantiate, subst_subst, instantiate, subst_subst]
  apply subst_congr
  intro C x
  cases x with
  | zero => rfl
  | succ x => exact (subst_single_weaken (subst σ a) (σ x)).symm

/-- **Substituting by an extended substitution, via lifting.** Let $\sigma$ be a substitution from
the typing context $\Gamma$ to the typing context $\Delta$, $s$ a term of type $B$ in the context
$\Gamma$ extended by a newest variable of type $A$, and $a$ a term of type $A$ in context
$\Delta$. Applying to $s$ the extension of $\sigma$ that sends the newest variable to $a$ gives the
same term as applying the lift of $\sigma$ to $s$ and then replacing the newest variable of the
result by $a$. -/
theorem subst_cons (σ : Sub Γ Δ) (body : Tm (A :: Γ) B) (a : Tm Δ A) :
    subst (Sub.cons a σ) body = instantiate (subst (Sub.lift σ) body) a := by
  rw [instantiate, subst_subst]
  apply subst_congr
  intro C x
  exact (Sub.lift_single_apply σ a x).symm

/-- **Instantiation is substitution by an extended identity.** Let $b$ be a term of type $B$ in
the context $\Gamma$ extended by a newest variable of type $A$, and $a$ a term of type $A$ in
$\Gamma$. Instantiating the newest variable of $b$ by $a$ gives the same term as applying to $b$
the substitution that sends the newest variable to $a$ and each older variable to itself, that
is, the extension of the identity substitution on $\Gamma$ by $a$. -/
theorem instantiate_eq_subst_cons (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    instantiate body a = subst (Sub.cons a Sub.id) body := by
  apply subst_congr
  intro C x
  cases x <;> rfl

end Tm

end Cslib.Languages.LambdaCalculus.Stlc
