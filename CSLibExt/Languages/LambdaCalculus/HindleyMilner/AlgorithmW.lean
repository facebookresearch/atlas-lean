/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Algorithm W and its soundness
-/
module

public import CSLibExt.Languages.LambdaCalculus.HindleyMilner.Typing

/-!
# Algorithm W and its soundness

Milner's Algorithm W infers a type for an expression, together with the
substitution it had to apply to the context.  It threads a counter `n` of fresh
type variables: every variable `var m` with `m ≥ n` is unused so far.

- A variable instantiates its scheme with fresh variables.
- `λx. e` gives `x` a fresh type variable `β` and infers `e`.
- `e₁ e₂` infers `e₁`, then `e₂` in the substituted context, and unifies the
  type of `e₁` with `τ₂ → β` for a fresh `β`.
- `let x = e₁ in e₂` infers `e₁`, generalizes its type in the substituted
  context, and infers `e₂`.

**Soundness**: if `W Γ e n = some (s, τ, n')` then `s Γ ⊢ e : τ`.  The proof uses
only that `unify` returns a unifier, the substitution lemma `HasType.subst`, and
the renaming argument of its `let` case (`HasType.let_substTy`).  Completeness
(principal types) is not proved here.

## Main definitions

- `Scheme.boundSup σ` : one more than the largest bound-variable index of `σ`.
- `W Γ e n : Option (Subst B × Ty B × ℕ)`, and `infer e` (W in the empty context).

## Main results

- `hasType_of_W_eq_some` : soundness of W.
- `hasType_of_infer_eq_some` : a type inferred for a closed expression is a type of it.

## References

- R. Milner, *A theory of type polymorphism in programming*, J. Comput. Syst. Sci.
  17(3), 1978, 348-375.
- L. Damas, R. Milner, *Principal type-schemes for functional programs*, POPL 1982.
- W. Naraschewski, T. Nipkow, *Type inference verified: Algorithm W in
  Isabelle/HOL*, J. Automated Reasoning 23, 1999, 299-318.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.HindleyMilner

open Cslib.Unification Cslib.Unification.Term Cslib.Unification.Subst

variable {B : Type u}

/-! ### Substitutions on contexts -/

theorem Scheme.substTy_var (σ : Scheme B) : σ.substTy Term.var = σ := subst_id σ

theorem Scheme.substTy_substTy (s t : Subst B) (σ : Scheme B) :
    (σ.substTy s).substTy t = σ.substTy (s ≫ t) := by
  rw [Scheme.substTy, Scheme.substTy, Scheme.substTy, subst_subst]
  congr 1
  funext x
  exact (toScheme_subst t (s x)).symm

theorem Ctx.subst_var (Γ : Ctx B) : Γ.subst Term.var = Γ := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    simp only [Ctx.subst, List.map_cons, Scheme.substTy_var] at ih ⊢
    rw [ih]

theorem Ctx.subst_subst (s t : Subst B) (Γ : Ctx B) :
    (Γ.subst s).subst t = Γ.subst (s ≫ t) := by
  simp [Ctx.subst, Scheme.substTy_substTy]

/-- The `let` rule after a substitution: if `e₁ : τ₁` in `Γ`, and `e₂` has type `τ₂` once `x`
is bound to the substituted generalization of `τ₁` in `s Γ`, then `let x = e₁ in e₂ : τ₂` in
`s Γ`. -/
theorem HasType.let_substTy {Γ : Ctx B} {x : String} {e₁ e₂ : Expr} {τ₁ τ₂ : Ty B}
    (s : Subst B) (h₁ : HasType Γ e₁ τ₁)
    (h₂ : HasType ((x, (gen Γ τ₁).substTy s) :: Γ.subst s) e₂ τ₂) :
    HasType (Γ.subst s) (.let_ x e₁ e₂) τ₂ := by
  let s' : Subst B := fun y ↦
    if y ∈ Γ.ftv then s y else Term.var (y + above (Γ.subst s).ftv)
  have hs'Γ : ∀ y, (Γ.subst s).lookup y = (Γ.subst s').lookup y :=
    Ctx.lookup_subst_congr fun y hy ↦ by simp [s', hy]
  have h₁' : HasType (Γ.subst s) e₁ (τ₁.subst s') :=
    (h₁.subst s').mono (Ctx.MoreGeneral.of_lookup_eq hs'Γ)
  exact HasType.let_ h₁' (h₂.mono ((Ctx.MoreGeneral.refl _).cons x
    (gen_subst_moreGeneral Γ τ₁ s)))

/-! ### The algorithm -/

/-- One more than the largest bound-variable index of a scheme (`0` if it has none). -/
def Scheme.boundSup : Scheme B → ℕ
  | Term.var _ => 0
  | Term.const (Sum.inl _) => 0
  | Term.const (Sum.inr i) => i + 1
  | Term.node l r => max (Scheme.boundSup l) (Scheme.boundSup r)

variable [DecidableEq B]

/-- Algorithm W. `W Γ e n` returns a substitution `s`, a type `τ`, and the next fresh
variable, or `none` when unification fails or a variable is unbound. Type variables
`var m` with `m ≥ n` are used as fresh. -/
def W (Γ : Ctx B) : Expr → ℕ → Option (Subst B × Ty B × ℕ)
  | .var x, n =>
    (Γ.lookup x).map fun σ ↦ (Term.var, σ.inst (fun i ↦ Term.var (n + i)), n + σ.boundSup)
  | .lam x e, n =>
    (W ((x, toScheme (Term.var n)) :: Γ) e (n + 1)).map fun (s, τ, n') ↦
      (s, node ((Term.var n).subst s) τ, n')
  | .app e₁ e₂, n => do
    let (s₁, τ₁, n₁) ← W Γ e₁ n
    let (s₂, τ₂, n₂) ← W (Γ.subst s₁) e₂ n₁
    let s₃ ← unify [(τ₁.subst s₂, node τ₂ (Term.var n₂))]
    return (s₁ ≫ s₂ ≫ s₃, (Term.var n₂).subst s₃, n₂ + 1)
  | .let_ x e₁ e₂, n => do
    let (s₁, τ₁, n₁) ← W Γ e₁ n
    let (s₂, τ₂, n₂) ← W ((x, gen (Γ.subst s₁) τ₁) :: Γ.subst s₁) e₂ n₁
    return (s₁ ≫ s₂, τ₂, n₂)
termination_by e => sizeOf e

/-- Type inference for closed expressions. -/
def infer (e : Expr) : Option (Ty B) := (W [] e 0).map fun r ↦ r.2.1

/-! ### Soundness -/

/-- **Soundness of Algorithm W**: a returned substitution `s` and type `τ` satisfy
`s Γ ⊢ e : τ`. -/
theorem hasType_of_W_eq_some {e : Expr} :
    ∀ {Γ : Ctx B} {n : ℕ} {s : Subst B} {τ : Ty B} {n' : ℕ},
      W Γ e n = some (s, τ, n') → HasType (Γ.subst s) e τ := by
  induction e with
  | var x =>
    intro Γ n s τ n' h
    rw [W] at h
    obtain ⟨σ, hσ, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    rw [Ctx.subst_var]
    exact HasType.var _ hσ
  | lam x e ih =>
    intro Γ n s τ n' h
    rw [W] at h
    obtain ⟨⟨s₀, τ₀, n₀⟩, h₀, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    have := ih h₀
    simp only [Ctx.subst, List.map_cons, ← toScheme_subst] at this
    exact HasType.lam this
  | app e₁ e₂ ih₁ ih₂ =>
    intro Γ n s τ n' h
    rw [W] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨s₁, τ₁, n₁⟩, h₁, ⟨s₂, τ₂, n₂⟩, h₂, s₃, h₃, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    have hu := unifies_cons.mp (unifies_unify h₃)
    have t₁ := (ih₁ h₁).subst (s₂ ≫ s₃)
    have t₂ := (ih₂ h₂).subst s₃
    dsimp only at hu t₂
    rw [Ctx.subst_subst, subst_comp, hu.1, subst_node, ← comp_assoc] at t₁
    rw [Ctx.subst_subst, Ctx.subst_subst, ← comp_assoc] at t₂
    exact HasType.app t₁ t₂
  | let_ x e₁ e₂ ih₁ ih₂ =>
    intro Γ n s τ n' h
    rw [W] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨s₁, τ₁, n₁⟩, h₁, ⟨s₂, τ₂, n₂⟩, h₂, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    have t₂ := ih₂ h₂
    simp only [Ctx.subst, List.map_cons] at t₂
    rw [← Ctx.subst_subst]
    exact HasType.let_substTy s₂ (ih₁ h₁) t₂

/-- A type inferred for a closed expression is a type of it. -/
theorem hasType_of_infer_eq_some {e : Expr} {τ : Ty B} (h : infer e = some τ) :
    HasType [] e τ := by
  obtain ⟨⟨s, τ', n'⟩, hW, rfl⟩ := Option.map_eq_some_iff.mp h
  simpa [Ctx.subst] using hasType_of_W_eq_some hW

end Cslib.HindleyMilner
