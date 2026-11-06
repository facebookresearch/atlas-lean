/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The simply typed lambda calculus with references: substitution laws
-/
module

public import CSLibExt.Languages.LambdaCalculus.References.Syntax

/-!
# Renaming and substitution laws

Constructor equations for `Term.rename` and `Term.subst`, and the laws of the
parallel renaming and substitution algebra: congruence, identity, composition
of renamings, and the interactions of renaming with substitution and of
substitution with itself.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.References

universe u

variable {Base : Type u}

namespace Term

section ConstructorEquations

variable (ρ : Nat → Nat) (σ : Nat → Term Base)

@[simp] theorem rename_var (x : Nat) : rename ρ (.var x : Term Base) = .var (ρ x) := rfl
@[simp] theorem rename_lam (T : Ty Base) (body : Term Base) :
    rename ρ (.lam T body) = .lam T (rename (liftRen ρ) body) := rfl
@[simp] theorem rename_app (f a : Term Base) :
    rename ρ (.app f a) = .app (rename ρ f) (rename ρ a) := rfl
@[simp] theorem rename_unit : rename ρ (.unit : Term Base) = .unit := rfl
@[simp] theorem rename_loc (l : Nat) : rename ρ (.loc l : Term Base) = .loc l := rfl
@[simp] theorem rename_ref (t : Term Base) : rename ρ (.ref t) = .ref (rename ρ t) := rfl
@[simp] theorem rename_deref (t : Term Base) : rename ρ (.deref t) = .deref (rename ρ t) := rfl
@[simp] theorem rename_assign (t₁ t₂ : Term Base) :
    rename ρ (.assign t₁ t₂) = .assign (rename ρ t₁) (rename ρ t₂) := rfl

@[simp] theorem subst_var (x : Nat) : subst σ (.var x) = σ x := rfl
@[simp] theorem subst_lam (T : Ty Base) (body : Term Base) :
    subst σ (.lam T body) = .lam T (subst (liftSub σ) body) := rfl
@[simp] theorem subst_app (f a : Term Base) :
    subst σ (.app f a) = .app (subst σ f) (subst σ a) := rfl
@[simp] theorem subst_unit : subst σ (.unit : Term Base) = .unit := rfl
@[simp] theorem subst_loc (l : Nat) : subst σ (.loc l : Term Base) = .loc l := rfl
@[simp] theorem subst_ref (t : Term Base) : subst σ (.ref t) = .ref (subst σ t) := rfl
@[simp] theorem subst_deref (t : Term Base) : subst σ (.deref t) = .deref (subst σ t) := rfl
@[simp] theorem subst_assign (t₁ t₂ : Term Base) :
    subst σ (.assign t₁ t₂) = .assign (subst σ t₁) (subst σ t₂) := rfl

end ConstructorEquations

/-- **Renaming respects pointwise equality.** Let $\rho, \rho' : \mathbb{N} \to \mathbb{N}$ be
renamings of de Bruijn variables with $\rho(x) = \rho'(x)$ for every $x \in \mathbb{N}$. Then for
every term $t$ of the simply typed lambda calculus with references, renaming $t$ by $\rho$ gives
the same term as renaming $t$ by $\rho'$. -/
theorem rename_congr {ρ ρ' : Nat → Nat} (h : ∀ x, ρ x = ρ' x) (t : Term Base) :
    rename ρ t = rename ρ' t := by
  induction t generalizing ρ ρ' with
  | var x => simp [h]
  | lam T body ih =>
      simp only [rename_lam]
      congr 1
      apply ih
      intro x
      cases x <;> simp [h]
  | app f a ihf iha => simp [ihf h, iha h]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih h]
  | deref t ih => simp [ih h]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁ h, ih₂ h]

/-- **Renaming by the identity.** For every term $t$ of the simply typed lambda calculus with
references, renaming the de Bruijn variables of $t$ by the identity map of $\mathbb{N}$ gives
back $t$. -/
@[simp] theorem rename_id (t : Term Base) : rename id t = t := by
  induction t with
  | var => rfl
  | lam T body ih =>
      simp only [rename_lam]
      rw [rename_congr (ρ' := id) (fun x => by cases x <;> rfl)]
      rw [ih]
  | app f a ihf iha => simp [ihf, iha]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih]
  | deref t ih => simp [ih]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- **Composition of renamings.** For all renamings $\rho, \rho' : \mathbb{N} \to \mathbb{N}$ of
de Bruijn variables and every term $t$ of the simply typed lambda calculus with references,
renaming $t$ by $\rho$ and then renaming the result by $\rho'$ gives the same term as renaming $t$
by the composite $\rho' \circ \rho$. -/
theorem rename_rename (ρ ρ' : Nat → Nat) (t : Term Base) :
    rename ρ' (rename ρ t) = rename (ρ' ∘ ρ) t := by
  induction t generalizing ρ ρ' with
  | var => rfl
  | lam T body ih =>
      simp only [rename_lam, ih]
      congr 1
      apply rename_congr
      intro x
      cases x <;> rfl
  | app f a ihf iha => simp [ihf, iha]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih]
  | deref t ih => simp [ih]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- **Substitution respects pointwise equality.** Let $\sigma, \sigma'$ be parallel substitutions,
each sending every de Bruijn index to a term of the simply typed lambda calculus with references,
with $\sigma(x) = \sigma'(x)$ for every $x \in \mathbb{N}$. Then for every term $t$, applying
$\sigma$ to $t$ gives the same term as applying $\sigma'$ to $t$. -/
theorem subst_congr {σ σ' : Nat → Term Base} (h : ∀ x, σ x = σ' x) (t : Term Base) :
    subst σ t = subst σ' t := by
  induction t generalizing σ σ' with
  | var x => simp [h]
  | lam T body ih =>
      simp only [subst_lam]
      congr 1
      apply ih
      intro x
      cases x <;> simp [h]
  | app f a ihf iha => simp [ihf h, iha h]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih h]
  | deref t ih => simp [ih h]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁ h, ih₂ h]

/-- **Substitution by variables is the identity.** For every term $t$ of the simply typed lambda
calculus with references, applying the parallel substitution that sends each de Bruijn index $x$
to the variable term $x$ gives back $t$. -/
@[simp] theorem subst_id (t : Term Base) : subst .var t = t := by
  induction t with
  | var => rfl
  | lam T body ih =>
      simp only [subst_lam]
      rw [subst_congr (σ' := .var) (fun x => by cases x <;> rfl)]
      rw [ih]
  | app f a ihf iha => simp [ihf, iha]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih]
  | deref t ih => simp [ih]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- **Renaming then substituting.** Let $\rho : \mathbb{N} \to \mathbb{N}$ be a renaming of de
Bruijn variables, $\sigma$ a parallel substitution sending each index to a term of the simply
typed lambda calculus with references, and $t$ a term. Renaming $t$ by $\rho$ and then applying
$\sigma$ gives the same term as applying the substitution $\sigma \circ \rho$ to $t$. -/
theorem subst_rename (ρ : Nat → Nat) (σ : Nat → Term Base) (t : Term Base) :
    subst σ (rename ρ t) = subst (σ ∘ ρ) t := by
  induction t generalizing ρ σ with
  | var => rfl
  | lam T body ih =>
      simp only [rename_lam, subst_lam, ih]
      congr 1
      apply subst_congr
      intro x
      cases x <;> rfl
  | app f a ihf iha => simp [ihf, iha]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih]
  | deref t ih => simp [ih]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- **Substituting then renaming.** Let $\rho : \mathbb{N} \to \mathbb{N}$ be a renaming of de
Bruijn variables, $\sigma$ a parallel substitution sending each index to a term of the simply
typed lambda calculus with references, and $t$ a term. Applying $\sigma$ to $t$ and then renaming
the result by $\rho$ gives the same term as applying to $t$ the substitution that sends each
index $x$ to the renaming of $\sigma(x)$ by $\rho$. -/
theorem rename_subst (ρ : Nat → Nat) (σ : Nat → Term Base) (t : Term Base) :
    rename ρ (subst σ t) = subst (rename ρ ∘ σ) t := by
  induction t generalizing ρ σ with
  | var => rfl
  | lam T body ih =>
      simp only [rename_lam, subst_lam, ih]
      congr 1
      apply subst_congr
      intro x
      cases x with
      | zero => rfl
      | succ x =>
          simp only [Function.comp_apply, liftSub_succ, rename_rename]
          exact rename_congr (fun _ => rfl) _
  | app f a ihf iha => simp [ihf, iha]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih]
  | deref t ih => simp [ih]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- **Composition of substitutions in the lambda calculus with references.** For all parallel
substitutions $\sigma, \tau$, each sending every de Bruijn index to a term of the simply typed
lambda calculus with references, and every term $t$, applying $\sigma$ to $t$ and then $\tau$ to
the result gives the same term as applying to $t$ the substitution that sends each index $x$ to
the result of applying $\tau$ to $\sigma(x)$. -/
theorem subst_subst (σ τ : Nat → Term Base) (t : Term Base) :
    subst τ (subst σ t) = subst (fun x => subst τ (σ x)) t := by
  induction t generalizing σ τ with
  | var => rfl
  | lam T body ih =>
      simp only [subst_lam, ih]
      congr 1
      apply subst_congr
      intro x
      cases x with
      | zero => rfl
      | succ x =>
          simp only [liftSub_succ, subst_rename, rename_subst]
          exact subst_congr (fun _ => rfl) _
  | app f a ihf iha => simp [ihf, iha]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih]
  | deref t ih => simp [ih]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- **Instantiating a shifted term.** For all terms $t$ and $s$ of the simply typed lambda calculus
with references, shift every free de Bruijn variable of $t$ up by one (rename by
$x \mapsto x + 1$), then instantiate the result with $s$, replacing variable $0$ by $s$ and
lowering every other variable $x + 1$ to $x$. The outcome is $t$. -/
@[simp] theorem instantiate_rename_succ (t s : Term Base) :
    (rename Nat.succ t).instantiate s = t := by
  rw [instantiate, subst_rename]
  exact (subst_congr (fun _ => rfl) t).trans (subst_id t)

end Term

end Cslib.Languages.LambdaCalculus.References
