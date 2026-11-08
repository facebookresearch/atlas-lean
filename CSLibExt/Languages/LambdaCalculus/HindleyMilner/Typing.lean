/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Let-polymorphic typing (Hindley-Milner)
-/
module

public import CSLibExt.Foundations.Unification.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Union

/-!
# Let-polymorphic typing (Hindley-Milner)

The Damas-Milner type system for the λ-calculus with `let`, in its
syntax-directed form: instantiation happens exactly at variables and
generalization exactly at `let`.

Monotypes are the unification terms of `CSLibExt/Foundations/Unification`:
type variables `var α`, base types `const b`, and `node τ₁ τ₂` read as
`τ₁ → τ₂`.  A type scheme is a term over `B ⊕ ℕ` whose constants `inr i` are the
bound variables.  Substitutions act only on `var`s, so applying one to a scheme
never captures a bound variable (as in Naraschewski and Nipkow's Isabelle
development).  Generalizing a type variable `α` turns it into the bound
variable `inr α`.

## Main definitions

- `Expr` : variables, application, abstraction, and `let`.
- `Scheme B`, `toScheme`, `Scheme.inst σ ts` (instantiate bound variable `i` by `ts i`).
- `Ctx B`, `Ctx.lookup`, `Ctx.ftv`, `Ctx.subst`, `gen Γ τ`.
- `HasType Γ e τ` : the syntax-directed typing relation.

## Main results

- `HasType.mono` : typing is preserved when the context is replaced by a more
  general one (`Ctx.MoreGeneral`).
- `HasType.subst` : typing is stable under type substitution,
  `Γ ⊢ e : τ → s Γ ⊢ e : s τ`, the key lemma for Algorithm W.
- `not_hasType_lam_self_app` : `λf. f f` has no type, while
  `let f = λx. x in f f` does (`hasType_let_id_app_id`); `let` is what makes
  `f` polymorphic.

## References

- L. Damas, R. Milner, *Principal type-schemes for functional programs*, POPL 1982.
- D. Clément, J. Despeyroux, T. Despeyroux, G. Kahn, *A simple applicative
  language: Mini-ML*, LFP 1986 (the syntax-directed system).
- W. Naraschewski, T. Nipkow, *Type inference verified: Algorithm W in
  Isabelle/HOL*, J. Automated Reasoning 23, 1999, 299-318.
- B. C. Pierce, *Types and Programming Languages*, MIT Press 2002, §22.7.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.HindleyMilner

open Cslib.Unification Cslib.Unification.Term Cslib.Unification.Subst

/-- Expressions of the λ-calculus with `let`, over named variables. -/
inductive Expr where
  | var (x : String)
  | app (e₁ e₂ : Expr)
  | lam (x : String) (e : Expr)
  | let_ (x : String) (e₁ e₂ : Expr)
  deriving DecidableEq, Repr

variable {B : Type u}

/-- Monotypes: type variables, base types, and arrows (`node`). -/
abbrev Ty (B : Type u) := Term B

/-- Type schemes: the constants `inr i` are bound variables. -/
abbrev Scheme (B : Type u) := Term (B ⊕ ℕ)

/-- A monotype as a scheme with no bound variables. -/
def toScheme : Ty B → Scheme B
  | var x => var x
  | const b => const (Sum.inl b)
  | node l r => node (toScheme l) (toScheme r)

/-- Evaluate a scheme: free variable `x` becomes `f x` and bound variable `i` becomes `g i`. -/
def Scheme.eval (f g : ℕ → Ty B) : Scheme B → Ty B
  | var x => f x
  | const (Sum.inl b) => const b
  | const (Sum.inr i) => g i
  | node l r => node (Scheme.eval f g l) (Scheme.eval f g r)

/-- Instantiate the bound variable `i` of a scheme by `ts i`. -/
def Scheme.inst (ts : ℕ → Ty B) (σ : Scheme B) : Ty B := σ.eval Term.var ts

/-- Apply a type substitution to the free variables of a scheme. -/
def Scheme.substTy (s : Subst B) (σ : Scheme B) : Scheme B := σ.subst fun x ↦ toScheme (s x)

theorem eval_toScheme (f g : ℕ → Ty B) (τ : Ty B) : (toScheme τ).eval f g = τ.subst f := by
  induction τ with
  | var x => rfl
  | const b => rfl
  | node l r ihl ihr => simp [toScheme, Scheme.eval, ihl, ihr]

theorem inst_toScheme (ts : ℕ → Ty B) (τ : Ty B) : (toScheme τ).inst ts = τ := by
  rw [Scheme.inst, eval_toScheme, subst_id]

theorem vars_toScheme (τ : Ty B) : (toScheme τ).vars = τ.vars := by
  induction τ with
  | var x => rfl
  | const b => rfl
  | node l r ihl ihr => simp [toScheme, Term.vars, ihl, ihr]

theorem toScheme_subst (s : Subst B) (τ : Ty B) :
    toScheme (τ.subst s) = (toScheme τ).substTy s := by
  induction τ with
  | var x => rfl
  | const b => rfl
  | node l r ihl ihr => simp [toScheme, Scheme.substTy, ihl, ihr] at *

theorem eval_substTy (s : Subst B) (f g : ℕ → Ty B) (σ : Scheme B) :
    (σ.substTy s).eval f g = σ.eval (fun x ↦ (s x).subst f) g := by
  induction σ with
  | var x => exact eval_toScheme _ _ _
  | const c => cases c <;> rfl
  | node l r ihl ihr =>
    simp only [Scheme.substTy, subst_node, Scheme.eval] at ihl ihr ⊢
    rw [ihl, ihr]

theorem subst_eval (s : Subst B) (f g : ℕ → Ty B) (σ : Scheme B) :
    (σ.eval f g).subst s = σ.eval (fun x ↦ (f x).subst s) (fun i ↦ (g i).subst s) := by
  induction σ with
  | var x => rfl
  | const c => cases c <;> rfl
  | node l r ihl ihr => simp [Scheme.eval, ihl, ihr]

/-- Instantiation commutes with substitution. -/
theorem inst_substTy (s : Subst B) (ts : ℕ → Ty B) (σ : Scheme B) :
    (σ.substTy s).inst (fun i ↦ (ts i).subst s) = (σ.inst ts).subst s := by
  rw [Scheme.inst, Scheme.inst, eval_substTy, subst_eval]
  simp [subst_id]

theorem vars_substTy_subset (s : Subst B) (σ : Scheme B) {z : ℕ}
    (hz : z ∈ (σ.substTy s).vars) : ∃ y ∈ σ.vars, z ∈ (s y).vars := by
  obtain ⟨y, hy, hzy⟩ := exists_of_mem_vars_subst hz
  exact ⟨y, hy, by simpa [vars_toScheme] using hzy⟩

theorem vars_subset_vars_substTy (s : Subst B) {σ : Scheme B} {y : ℕ} (hy : y ∈ σ.vars) :
    (s y).vars ⊆ (σ.substTy s).vars := by
  have := vars_subset_vars_subst (s := fun x ↦ toScheme (s x)) hy
  simpa [Scheme.substTy, vars_toScheme] using this

/-- Substitutions that agree on the free variables of a scheme act on it alike. -/
theorem substTy_congr {s t : Subst B} {σ : Scheme B} (h : ∀ x ∈ σ.vars, s x = t x) :
    σ.substTy s = σ.substTy t :=
  subst_congr fun x hx ↦ by rw [h x hx]

/-! ### Contexts and generalization -/

/-- Typing contexts: the first binding of a name is the visible one. -/
abbrev Ctx (B : Type u) := List (String × Scheme B)

/-- The visible scheme of a name. -/
def Ctx.lookup : Ctx B → String → Option (Scheme B)
  | [], _ => none
  | (y, σ) :: Γ, x => if x = y then some σ else Ctx.lookup Γ x

theorem Ctx.lookup_cons (y x : String) (σ : Scheme B) (Γ : Ctx B) :
    Ctx.lookup ((y, σ) :: Γ) x = if x = y then some σ else Γ.lookup x := rfl

theorem Ctx.mem_names_of_lookup {Γ : Ctx B} {x : String} {σ : Scheme B}
    (h : Γ.lookup x = some σ) : x ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil => simp [Ctx.lookup] at h
  | cons p Γ ih =>
    obtain ⟨y, σ'⟩ := p
    rw [Ctx.lookup_cons] at h
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [hxy, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- The free type variables of the visible scheme of a name. -/
def Ctx.visibleVars (Γ : Ctx B) (x : String) : Finset ℕ :=
  match Γ.lookup x with
  | some σ => σ.vars
  | none => ∅

/-- The free type variables of a context: those of its visible bindings. A binding shadowed
by an earlier one with the same name does not count, so `Γ.ftv` depends only on `Γ.lookup`. -/
def Ctx.ftv (Γ : Ctx B) : Finset ℕ := (Γ.map Prod.fst).toFinset.biUnion Γ.visibleVars

theorem Ctx.mem_ftv {Γ : Ctx B} {z : ℕ} :
    z ∈ Γ.ftv ↔ ∃ x σ, Γ.lookup x = some σ ∧ z ∈ σ.vars := by
  simp only [Ctx.ftv, Finset.mem_biUnion, List.mem_toFinset, Ctx.visibleVars]
  constructor
  · rintro ⟨x, -, hz⟩
    split at hz
    · next σ hσ => exact ⟨x, σ, hσ, hz⟩
    · simp at hz
  · rintro ⟨x, σ, hσ, hz⟩
    exact ⟨x, Ctx.mem_names_of_lookup hσ, by simp [hσ, hz]⟩

/-- Contexts with the same lookups have the same free type variables. -/
theorem Ctx.ftv_congr {Γ Γ' : Ctx B} (h : ∀ x, Γ.lookup x = Γ'.lookup x) : Γ.ftv = Γ'.ftv := by
  ext z
  simp only [Ctx.mem_ftv, h]

theorem Ctx.ftv_cons_subset (x : String) (σ : Scheme B) (Γ : Ctx B) :
    Ctx.ftv ((x, σ) :: Γ) ⊆ σ.vars ∪ Γ.ftv := by
  intro z hz
  obtain ⟨y, σ', hσ', hz⟩ := Ctx.mem_ftv.mp hz
  rw [Ctx.lookup_cons] at hσ'
  by_cases hyx : y = x
  · simp only [hyx, ↓reduceIte, Option.some.injEq] at hσ'
    subst hσ'
    exact Finset.mem_union_left _ hz
  · simp only [hyx, ↓reduceIte] at hσ'
    exact Finset.mem_union_right _ (Ctx.mem_ftv.mpr ⟨y, σ', hσ', hz⟩)

theorem Ctx.vars_subset_ftv_cons (x : String) (σ : Scheme B) (Γ : Ctx B) :
    σ.vars ⊆ Ctx.ftv ((x, σ) :: Γ) := fun z hz ↦
  Ctx.mem_ftv.mpr ⟨x, σ, by simp [Ctx.lookup_cons], hz⟩

/-- Apply a type substitution to every scheme of a context. -/
def Ctx.subst (s : Subst B) (Γ : Ctx B) : Ctx B := Γ.map fun p ↦ (p.1, p.2.substTy s)

theorem Ctx.lookup_subst (s : Subst B) (Γ : Ctx B) (x : String) :
    (Γ.subst s).lookup x = (Γ.lookup x).map (Scheme.substTy s) := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    obtain ⟨y, σ⟩ := p
    rw [show Ctx.subst s ((y, σ) :: Γ) = (y, σ.substTy s) :: Ctx.subst s Γ from rfl,
      Ctx.lookup_cons, Ctx.lookup_cons]
    by_cases hxy : x = y
    · simp only [hxy, ↓reduceIte, Option.map_some]
    · simp only [hxy, ↓reduceIte]
      exact ih

theorem Ctx.vars_subset_ftv_of_lookup {Γ : Ctx B} {x : String} {σ : Scheme B}
    (h : Γ.lookup x = some σ) : σ.vars ⊆ Γ.ftv := fun _ hz ↦
  Ctx.mem_ftv.mpr ⟨x, σ, h, hz⟩

/-- Substitutions agreeing on the free variables of a context give the same lookups. -/
theorem Ctx.lookup_subst_congr {s t : Subst B} {Γ : Ctx B} (h : ∀ x ∈ Γ.ftv, s x = t x)
    (x : String) : (Γ.subst s).lookup x = (Γ.subst t).lookup x := by
  rw [Ctx.lookup_subst, Ctx.lookup_subst]
  cases hx : Γ.lookup x with
  | none => rfl
  | some σ =>
    simp only [Option.map_some]
    rw [substTy_congr fun y hy ↦ h y (Ctx.vars_subset_ftv_of_lookup hx hy)]

theorem Ctx.mem_ftv_subst {s : Subst B} {Γ : Ctx B} {z : ℕ} (hz : z ∈ (Γ.subst s).ftv) :
    ∃ y ∈ Γ.ftv, z ∈ (s y).vars := by
  obtain ⟨x, σ', hσ', hz⟩ := Ctx.mem_ftv.mp hz
  rw [Ctx.lookup_subst] at hσ'
  obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp hσ'
  obtain ⟨y, hy, hzy⟩ := vars_substTy_subset s σ hz
  exact ⟨y, Ctx.vars_subset_ftv_of_lookup hσ hy, hzy⟩

theorem Ctx.vars_subset_ftv_subst {s : Subst B} {Γ : Ctx B} {y : ℕ} (hy : y ∈ Γ.ftv) :
    (s y).vars ⊆ (Γ.subst s).ftv := by
  obtain ⟨x, σ, hσ, hy⟩ := Ctx.mem_ftv.mp hy
  refine (vars_subset_vars_substTy s hy).trans (Ctx.vars_subset_ftv_of_lookup (x := x) ?_)
  rw [Ctx.lookup_subst, hσ]
  rfl

/-- Generalize the type variables of `τ` that are not free in `Γ`: `α` becomes the bound
variable `inr α`. -/
def gen (Γ : Ctx B) (τ : Ty B) : Scheme B :=
  (toScheme τ).subst fun x ↦ if x ∈ Γ.ftv then var x else const (Sum.inr x)

theorem eval_gen (Γ : Ctx B) (τ : Ty B) (f g : ℕ → Ty B) :
    (gen Γ τ).eval f g = τ.subst fun x ↦ if x ∈ Γ.ftv then f x else g x := by
  induction τ with
  | var x =>
    by_cases hx : x ∈ Γ.ftv <;> simp [gen, toScheme, hx, Scheme.eval]
  | const b => rfl
  | node l r ihl ihr =>
    simp only [gen, toScheme, subst_node, Scheme.eval] at ihl ihr ⊢
    rw [ihl, ihr]

theorem inst_gen (Γ : Ctx B) (τ : Ty B) (ts : ℕ → Ty B) :
    (gen Γ τ).inst ts = τ.subst fun x ↦ if x ∈ Γ.ftv then Term.var x else ts x :=
  eval_gen Γ τ _ _

theorem vars_gen (Γ : Ctx B) (τ : Ty B) : (gen Γ τ).vars = τ.vars.filter (· ∈ Γ.ftv) := by
  induction τ with
  | var x =>
    by_cases hx : x ∈ Γ.ftv <;> simp [gen, toScheme, hx, Term.vars, Finset.filter_singleton]
  | const b => simp [gen, toScheme, Term.vars]
  | node l r ihl ihr =>
    simp only [gen, toScheme, subst_node, Term.vars] at ihl ihr ⊢
    rw [ihl, ihr, Finset.filter_union]

/-! ### Typing -/

/-- The syntax-directed Damas-Milner typing relation. -/
inductive HasType : Ctx B → Expr → Ty B → Prop
  /-- A variable has every instance of its scheme. -/
  | var {Γ : Ctx B} {x : String} {σ : Scheme B} (ts : ℕ → Ty B) :
      Γ.lookup x = some σ → HasType Γ (.var x) (σ.inst ts)
  | app {Γ : Ctx B} {e₁ e₂ : Expr} {τ₁ τ₂ : Ty B} :
      HasType Γ e₁ (node τ₁ τ₂) → HasType Γ e₂ τ₁ → HasType Γ (.app e₁ e₂) τ₂
  /-- An abstraction binds a monotype. -/
  | lam {Γ : Ctx B} {x : String} {e : Expr} {τ₁ τ₂ : Ty B} :
      HasType ((x, toScheme τ₁) :: Γ) e τ₂ → HasType Γ (.lam x e) (node τ₁ τ₂)
  /-- `let` generalizes the type of the bound expression. -/
  | let_ {Γ : Ctx B} {x : String} {e₁ e₂ : Expr} {τ₁ τ₂ : Ty B} :
      HasType Γ e₁ τ₁ → HasType ((x, gen Γ τ₁) :: Γ) e₂ τ₂ → HasType Γ (.let_ x e₁ e₂) τ₂

/-! ### More general contexts -/

/-- `σ'` is more general than `σ`: every instance of `σ` is one of `σ'`, and `σ'` has no
other free variables. -/
def Scheme.MoreGeneral (σ' σ : Scheme B) : Prop :=
  (∀ ts, ∃ ts', σ'.inst ts' = σ.inst ts) ∧ σ'.vars ⊆ σ.vars

theorem Scheme.MoreGeneral.refl (σ : Scheme B) : σ.MoreGeneral σ :=
  ⟨fun ts ↦ ⟨ts, rfl⟩, Finset.Subset.refl _⟩

/-- `Γ'` is more general than `Γ`: the same names are visible, each with a more general
scheme. Only lookups matter, so shadowed bindings play no role. -/
def Ctx.MoreGeneral (Γ' Γ : Ctx B) : Prop :=
  (∀ x σ, Γ.lookup x = some σ → ∃ σ', Γ'.lookup x = some σ' ∧ σ'.MoreGeneral σ) ∧
    ∀ x σ', Γ'.lookup x = some σ' → ∃ σ, Γ.lookup x = some σ ∧ σ'.MoreGeneral σ

theorem Ctx.MoreGeneral.lookup {Γ' Γ : Ctx B} (h : Γ'.MoreGeneral Γ) {x : String}
    {σ : Scheme B} (hx : Γ.lookup x = some σ) :
    ∃ σ', Γ'.lookup x = some σ' ∧ σ'.MoreGeneral σ :=
  h.1 x σ hx

theorem Ctx.MoreGeneral.ftv_subset {Γ' Γ : Ctx B} (h : Γ'.MoreGeneral Γ) : Γ'.ftv ⊆ Γ.ftv := by
  intro z hz
  obtain ⟨x, σ', hσ', hz⟩ := Ctx.mem_ftv.mp hz
  obtain ⟨σ, hσ, hg⟩ := h.2 x σ' hσ'
  exact Ctx.mem_ftv.mpr ⟨x, σ, hσ, hg.2 hz⟩

/-- Contexts with the same lookups are each more general than the other. -/
theorem Ctx.MoreGeneral.of_lookup_eq {Γ' Γ : Ctx B} (h : ∀ x, Γ'.lookup x = Γ.lookup x) :
    Γ'.MoreGeneral Γ :=
  ⟨fun x σ hσ ↦ ⟨σ, (h x).trans hσ, Scheme.MoreGeneral.refl σ⟩,
    fun x σ' hσ' ↦ ⟨σ', (h x).symm.trans hσ', Scheme.MoreGeneral.refl σ'⟩⟩

theorem Ctx.MoreGeneral.refl (Γ : Ctx B) : Γ.MoreGeneral Γ :=
  Ctx.MoreGeneral.of_lookup_eq fun _ ↦ rfl

/-- Extending both contexts with a binding of the same name keeps them related. -/
theorem Ctx.MoreGeneral.cons {Γ' Γ : Ctx B} (h : Γ'.MoreGeneral Γ) (x : String)
    {σ' σ : Scheme B} (hσ : σ'.MoreGeneral σ) :
    Ctx.MoreGeneral ((x, σ') :: Γ') ((x, σ) :: Γ) := by
  constructor
  · intro y ρ hρ
    rw [Ctx.lookup_cons] at hρ ⊢
    by_cases hyx : y = x
    · simp only [hyx, ↓reduceIte, Option.some.injEq] at hρ ⊢
      exact ⟨σ', rfl, hρ ▸ hσ⟩
    · simp only [hyx, ↓reduceIte] at hρ ⊢
      exact h.1 y ρ hρ
  · intro y ρ' hρ'
    rw [Ctx.lookup_cons] at hρ' ⊢
    by_cases hyx : y = x
    · simp only [hyx, ↓reduceIte, Option.some.injEq] at hρ' ⊢
      exact ⟨σ, rfl, hρ' ▸ hσ⟩
    · simp only [hyx, ↓reduceIte] at hρ' ⊢
      exact h.2 y ρ' hρ'

/-- Generalizing with respect to a context with fewer free variables is more general. -/
theorem gen_moreGeneral {Γ' Γ : Ctx B} (h : Γ'.ftv ⊆ Γ.ftv) (τ : Ty B) :
    (gen Γ' τ).MoreGeneral (gen Γ τ) := by
  refine ⟨fun ts ↦ ⟨fun x ↦ if x ∈ Γ.ftv then Term.var x else ts x, ?_⟩, ?_⟩
  · rw [inst_gen, inst_gen]
    refine subst_congr fun x _ ↦ ?_
    by_cases hx' : x ∈ Γ'.ftv
    · simp [hx', h hx']
    · simp [hx']
  · intro z hz
    rw [vars_gen, Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, h hz.2⟩

/-- **Generality**: a derivation stays valid in a more general context. -/
theorem HasType.mono {Γ : Ctx B} {e : Expr} {τ : Ty B} (hτ : HasType Γ e τ) :
    ∀ {Γ' : Ctx B}, Γ'.MoreGeneral Γ → HasType Γ' e τ := by
  induction hτ with
  | var ts hx =>
    intro Γ' hΓ
    obtain ⟨σ', hσ', hg⟩ := hΓ.lookup hx
    obtain ⟨ts', hts'⟩ := hg.1 ts
    rw [← hts']
    exact HasType.var ts' hσ'
  | app _ _ ih₁ ih₂ => exact fun hΓ ↦ HasType.app (ih₁ hΓ) (ih₂ hΓ)
  | @lam Γ x e τ₁ τ₂ _ ih =>
    intro Γ' hΓ
    exact HasType.lam (ih (hΓ.cons x (Scheme.MoreGeneral.refl _)))
  | @let_ Γ x e₁ e₂ τ₁ τ₂ _ _ ih₁ ih₂ =>
    intro Γ' hΓ
    exact HasType.let_ (ih₁ hΓ) (ih₂ (hΓ.cons x (gen_moreGeneral hΓ.ftv_subset τ₁)))

/-! ### Stability under substitution -/

/-- A natural number above every element of a finite set. -/
def above (S : Finset ℕ) : ℕ := S.sup id + 1

theorem lt_above {S : Finset ℕ} {x : ℕ} (hx : x ∈ S) : x < above S :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)

/-- The renaming step of the substitution lemma: after renaming the generalized variables of
`τ` above `N`, generalizing in `s Γ` is more general than substituting into `gen Γ τ`. -/
theorem gen_subst_moreGeneral (Γ : Ctx B) (τ : Ty B) (s : Subst B) :
    (gen (Γ.subst s) (τ.subst fun y ↦
        if y ∈ Γ.ftv then s y else Term.var (y + above (Γ.subst s).ftv))).MoreGeneral
      ((gen Γ τ).substTy s) := by
  set N := above (Γ.subst s).ftv
  refine ⟨fun ts ↦ ⟨fun z ↦ if N ≤ z then ts (z - N) else Term.var z, ?_⟩, ?_⟩
  · rw [inst_gen, Scheme.inst, eval_substTy, eval_gen, subst_subst]
    refine subst_congr fun y _ ↦ ?_
    by_cases hy : y ∈ Γ.ftv
    · simp only [hy, ↓reduceIte, subst_id]
      conv_rhs => rw [← subst_id (s y)]
      refine subst_congr fun z hz ↦ ?_
      have : z ∈ (Γ.subst s).ftv := Ctx.vars_subset_ftv_subst hy hz
      simp [this]
    · have hN : y + N ∉ (Γ.subst s).ftv := fun h ↦ absurd (lt_above h) (by omega)
      simp [hy, hN]
  · intro z hz
    rw [vars_gen, Finset.mem_filter] at hz
    obtain ⟨hz₁, hz₂⟩ := hz
    obtain ⟨y, hy, hzy⟩ := exists_of_mem_vars_subst hz₁
    by_cases hyΓ : y ∈ Γ.ftv
    · simp only [hyΓ, ↓reduceIte] at hzy
      refine vars_subset_vars_substTy s ?_ hzy
      rw [vars_gen, Finset.mem_filter]
      exact ⟨hy, hyΓ⟩
    · simp only [hyΓ, ↓reduceIte, Term.vars, Finset.mem_singleton] at hzy
      subst hzy
      exact absurd (lt_above hz₂) (by omega)

/-- **Substitution lemma**: `Γ ⊢ e : τ` gives `s Γ ⊢ e : s τ` for every type substitution. -/
theorem HasType.subst {Γ : Ctx B} {e : Expr} {τ : Ty B} (hτ : HasType Γ e τ) :
    ∀ s : Subst B, HasType (Γ.subst s) e (τ.subst s) := by
  induction hτ with
  | @var Γ x σ ts hx =>
    intro s
    rw [← inst_substTy]
    exact HasType.var _ (by rw [Ctx.lookup_subst, hx]; rfl)
  | app _ _ ih₁ ih₂ => exact fun s ↦ HasType.app (ih₁ s) (ih₂ s)
  | @lam Γ x e τ₁ τ₂ _ ih =>
    intro s
    have := ih s
    simp only [Ctx.subst, List.map_cons, ← toScheme_subst] at this
    exact HasType.lam this
  | @let_ Γ x e₁ e₂ τ₁ τ₂ _ _ ih₁ ih₂ =>
    intro s
    -- rename the generalized variables of `τ₁` above everything free in `s Γ`
    let s' : Subst B := fun y ↦
      if y ∈ Γ.ftv then s y else Term.var (y + above (Γ.subst s).ftv)
    have hs'Γ : ∀ y, (Γ.subst s).lookup y = (Γ.subst s').lookup y :=
      Ctx.lookup_subst_congr fun y hy ↦ by simp [s', hy]
    have h₁ : HasType (Γ.subst s) e₁ (τ₁.subst s') :=
      (ih₁ s').mono (Ctx.MoreGeneral.of_lookup_eq hs'Γ)
    have h₂ := ih₂ s
    simp only [Ctx.subst, List.map_cons] at h₂
    exact HasType.let_ h₁ (h₂.mono ((Ctx.MoreGeneral.refl _).cons x
      (gen_subst_moreGeneral Γ τ₁ s)))

/-! ### Inversion -/

theorem hasType_var_iff {Γ : Ctx B} {x : String} {τ : Ty B} :
    HasType Γ (.var x) τ ↔ ∃ σ ts, Γ.lookup x = some σ ∧ τ = σ.inst ts := by
  constructor
  · intro h
    cases h with
    | var ts hx => exact ⟨_, ts, hx, rfl⟩
  · rintro ⟨σ, ts, hx, rfl⟩
    exact HasType.var ts hx

theorem hasType_app_iff {Γ : Ctx B} {e₁ e₂ : Expr} {τ : Ty B} :
    HasType Γ (.app e₁ e₂) τ ↔ ∃ τ₁, HasType Γ e₁ (node τ₁ τ) ∧ HasType Γ e₂ τ₁ := by
  constructor
  · intro h
    cases h with
    | app h₁ h₂ => exact ⟨_, h₁, h₂⟩
  · rintro ⟨τ₁, h₁, h₂⟩
    exact HasType.app h₁ h₂

theorem hasType_lam_iff {Γ : Ctx B} {x : String} {e : Expr} {τ : Ty B} :
    HasType Γ (.lam x e) τ ↔
      ∃ τ₁ τ₂, τ = node τ₁ τ₂ ∧ HasType ((x, toScheme τ₁) :: Γ) e τ₂ := by
  constructor
  · intro h
    cases h with
    | lam h => exact ⟨_, _, rfl, h⟩
  · rintro ⟨τ₁, τ₂, rfl, h⟩
    exact HasType.lam h

theorem hasType_let_iff {Γ : Ctx B} {x : String} {e₁ e₂ : Expr} {τ : Ty B} :
    HasType Γ (.let_ x e₁ e₂) τ ↔
      ∃ τ₁, HasType Γ e₁ τ₁ ∧ HasType ((x, gen Γ τ₁) :: Γ) e₂ τ := by
  constructor
  · intro h
    cases h with
    | let_ h₁ h₂ => exact ⟨_, h₁, h₂⟩
  · rintro ⟨τ₁, h₁, h₂⟩
    exact HasType.let_ h₁ h₂

/-! ### Examples: `let` makes the bound variable polymorphic -/

/-- No monotype is an arrow from itself. -/
theorem ne_node_self_left (τ₁ τ₂ : Ty B) : τ₁ ≠ node τ₁ τ₂ := fun h ↦ by
  have := congrArg Term.size h
  simp only [Term.size] at this
  omega

/-- **Self-application has no type**: in `λf. f f`, `f` is λ-bound and so monomorphic. -/
theorem not_hasType_lam_self_app (Γ : Ctx B) (f : String) (τ : Ty B) :
    ¬ HasType Γ (.lam f (.app (.var f) (.var f))) τ := by
  rw [hasType_lam_iff]
  rintro ⟨τ₁, τ₂, -, h⟩
  obtain ⟨τ₀, h₁, h₂⟩ := hasType_app_iff.mp h
  obtain ⟨σ₁, ts₁, hx₁, he₁⟩ := hasType_var_iff.mp h₁
  obtain ⟨σ₂, ts₂, hx₂, he₂⟩ := hasType_var_iff.mp h₂
  simp only [Ctx.lookup, ↓reduceIte, Option.some.injEq] at hx₁ hx₂
  subst hx₁ hx₂
  rw [inst_toScheme] at he₁ he₂
  subst he₂
  exact ne_node_self_left τ₀ τ₂ he₁.symm

/-- **`let` generalizes**: `let f = λx. x in f f` has type `α → α`. -/
theorem hasType_let_id_app_id (Γ : Ctx B) (f x : String) (α : ℕ) :
    HasType Γ (.let_ f (.lam x (.var x)) (.app (.var f) (.var f)))
      (node (Term.var α) (Term.var α)) := by
  -- type the identity at a variable `β` that is fresh for `Γ`, so `gen` quantifies it
  set β := above Γ.ftv
  have hβ : β ∉ Γ.ftv := fun h ↦ absurd (lt_above h) (lt_irrefl _)
  have hid : HasType ((x, toScheme (Term.var β)) :: Γ) (.var x) (Term.var β) := by
    have h := HasType.var (Γ := (x, toScheme (Term.var β)) :: Γ) (x := x)
      (σ := toScheme (Term.var β)) (fun _ ↦ Term.var β) (by simp [Ctx.lookup])
    rwa [inst_toScheme] at h
  let Γ' : Ctx B := (f, gen Γ (node (Term.var β) (Term.var β))) :: Γ
  have hf₁ : HasType Γ' (.var f) (node (node (Term.var α) (Term.var α))
      (node (Term.var α) (Term.var α))) := by
    have h := HasType.var (Γ := Γ') (x := f) (σ := gen Γ (node (Term.var β) (Term.var β)))
      (fun _ ↦ node (Term.var α) (Term.var α)) (by simp [Γ', Ctx.lookup])
    simpa [inst_gen, hβ] using h
  have hf₂ : HasType Γ' (.var f) (node (Term.var α) (Term.var α)) := by
    have h := HasType.var (Γ := Γ') (x := f) (σ := gen Γ (node (Term.var β) (Term.var β)))
      (fun _ ↦ Term.var α) (by simp [Γ', Ctx.lookup])
    simpa [inst_gen, hβ] using h
  exact HasType.let_ (HasType.lam hid) (HasType.app hf₁ hf₂)

end Cslib.HindleyMilner
