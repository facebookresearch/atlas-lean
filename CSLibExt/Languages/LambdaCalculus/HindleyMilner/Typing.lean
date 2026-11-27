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

/-- **Expressions of the λ-calculus with let.** An expression is a variable $x$, an application
$e_1\,e_2$, an abstraction $\lambda x.\, e$, or a let-binding
$\mathsf{let}\ x = e_1\ \mathsf{in}\ e_2$, where $e$, $e_1$, $e_2$ are expressions and variable
names $x$ are strings. -/
inductive Expr where
  | var (x : String)
  | app (e₁ e₂ : Expr)
  | lam (x : String) (e : Expr)
  | let_ (x : String) (e₁ e₂ : Expr)
  deriving DecidableEq, Repr

variable {B : Type u}

/-- **Monotypes.** A monotype over a set $B$ of base types is a term over the constants $B$: a
type variable $\alpha \in \mathbb{N}$, a base type $b \in B$, or an arrow $\tau_1 \to \tau_2$ of
two monotypes (a binary node). -/
abbrev Ty (B : Type u) := Term B

/-- **Type schemes.** A type scheme over base types $B$ is a term over the constant set
$B \oplus \mathbb{N}$: its variables $\alpha \in \mathbb{N}$ are the free type variables, a constant
$\mathrm{inl}\, b$ is the base type $b \in B$, a constant $\mathrm{inr}\, i$ is the bound variable
$i$, and a node of two schemes is an arrow. -/
abbrev Scheme (B : Type u) := Term (B ⊕ ℕ)

/-- **Monotypes as type schemes.** Every monotype $\tau$ is read as the type scheme with no bound
variables of the same shape: a type variable stays the same type variable, a base type $b$
becomes the constant $\mathrm{inl}\, b$, and an arrow $\tau_1 \to \tau_2$ becomes the arrow of the
images of $\tau_1$ and $\tau_2$. -/
def toScheme : Ty B → Scheme B
  | var x => var x
  | const b => const (Sum.inl b)
  | node l r => node (toScheme l) (toScheme r)

/-- **Evaluation of a type scheme.** Given maps $f$ and $g$ from natural numbers to monotypes
over $B$, a type scheme $\sigma$ over $B$ evaluates to the monotype obtained by replacing each
free type variable $x$ of $\sigma$ by $f(x)$ and each bound variable $i$ by $g(i)$, keeping
every base type $b$ unchanged. An arrow $\sigma_1 \to \sigma_2$ evaluates to the arrow from the
evaluation of $\sigma_1$ to the evaluation of $\sigma_2$. -/
def Scheme.eval (f g : ℕ → Ty B) : Scheme B → Ty B
  | var x => f x
  | const (Sum.inl b) => const b
  | const (Sum.inr i) => g i
  | node l r => node (Scheme.eval f g l) (Scheme.eval f g r)

/-- **Instantiation of a type scheme.** Given monotypes $(t_i)_{i \in \mathbb{N}}$, the instance of
a scheme $\sigma$ at $(t_i)$ is the monotype obtained from $\sigma$ by replacing each bound
variable $i$ by $t_i$, keeping its free type variables and base types unchanged. -/
def Scheme.inst (ts : ℕ → Ty B) (σ : Scheme B) : Ty B := σ.eval Term.var ts

/-- **Applying a type substitution to a scheme.** For a type substitution $s$ and a type
scheme $\sigma$, $s\sigma$ is the scheme obtained from $\sigma$ by replacing every free type
variable $x$ with the monotype $s(x)$, read as a scheme with no bound variables. The bound
variables of $\sigma$ are left unchanged. -/
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

/-- **Instantiation commutes with substitution.** For every type substitution $s$, every scheme
$\sigma$ and all monotypes $(t_i)_{i \in \mathbb{N}}$, instantiating each bound variable $i$ of
$s(\sigma)$ by $s(t_i)$ gives $s$ applied to the instance of $\sigma$ at $(t_i)$. Here $s$ acts on
a scheme through its free type variables only. -/
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

/-- **Substitution into a scheme depends only on its free variables.** If two type
substitutions $s$ and $t$ satisfy $s(x) = t(x)$ for every free type variable $x$ of a type
scheme $\sigma$, then applying $s$ to $\sigma$ gives the same scheme as applying $t$. -/
theorem substTy_congr {s t : Subst B} {σ : Scheme B} (h : ∀ x ∈ σ.vars, s x = t x) :
    σ.substTy s = σ.substTy t :=
  subst_congr fun x hx ↦ by rw [h x hx]

/-! ### Contexts and generalization -/

/-- **Typing context.** A typing context over base types $B$ is a finite list of bindings
$(x, \sigma)$, each pairing a name $x$ (a string) with a type scheme $\sigma$ over $B$. A name
may be bound more than once; the first binding of a name in the list is the visible one. -/
abbrev Ctx (B : Type u) := List (String × Scheme B)

/-- **Context lookup.** The lookup of a name $x$ in a typing context $\Gamma$ is the scheme of the
first binding of $x$ in $\Gamma$ (the visible one), or nothing if $\Gamma$ has no binding of $x$. -/
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

/-- **Free type variables of a name's visible scheme.** For a typing context $\Gamma$ and a
name $x$, this is the set of free type variables of the scheme that $\Gamma$ binds to $x$ (the
first binding of $x$ in $\Gamma$), or the empty set if $\Gamma$ does not bind $x$. -/
def Ctx.visibleVars (Γ : Ctx B) (x : String) : Finset ℕ :=
  match Γ.lookup x with
  | some σ => σ.vars
  | none => ∅

/-- **Free type variables of a context.** The free type variables of a typing context $\Gamma$
are the type variables occurring free in the visible scheme of some name bound in $\Gamma$.

A binding shadowed by an earlier binding of the same name does not count, so the free type
variables of $\Gamma$ depend only on the visible scheme of each name. -/
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

/-- **Free type variables depend only on visible bindings.** If two typing contexts $\Gamma$ and
$\Gamma'$ give every name $x$ the same visible scheme (or both bind no scheme to $x$), then
$\Gamma$ and $\Gamma'$ have the same free type variables. -/
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

/-- **Applying a type substitution to a context.** For a type substitution $s$ and a typing
context $\Gamma$, $s\Gamma$ is the context obtained by applying $s$ to the scheme of every binding
of $\Gamma$, keeping the names and their order. -/
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

/-- **Substitutions agreeing on a context give the same lookups.** If two type substitutions $s$
and $t$ agree on every free type variable of a context $\Gamma$, then for every name $x$ the
lookups of $x$ in $s(\Gamma)$ and in $t(\Gamma)$ are equal: both give no scheme, or both give the
same scheme. -/
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

/-- **Generalization of a monotype.** Given a typing context $\Gamma$ and a monotype $\tau$, the
generalization of $\tau$ with respect to $\Gamma$ is the type scheme obtained from $\tau$ by
turning each type variable $\alpha$ that is not free in $\Gamma$ into the bound variable with
index $\alpha$, while type variables free in $\Gamma$ stay free. -/
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

/-- **Hindley–Milner typing.** The syntax-directed Damas–Milner typing relation
$\Gamma \vdash e : \tau$ between a context $\Gamma$, an expression $e$ and a monotype $\tau$ is the
least relation closed under the following rules, where $\Gamma, x : \sigma$ is $\Gamma$ extended
by the binding $x : \sigma$ in front.

- Variable: if the lookup of $x$ in $\Gamma$ gives the scheme $\sigma$, then
  $\Gamma \vdash x : \tau$ for every instance $\tau$ of $\sigma$, obtained by replacing each bound
  variable $i$ of $\sigma$ by a monotype $t_i$.
- Application: if $\Gamma \vdash e_1 : \tau_1 \to \tau_2$ and $\Gamma \vdash e_2 : \tau_1$, then
  $\Gamma \vdash e_1\, e_2 : \tau_2$.
- Abstraction: if $\Gamma, x : \tau_1 \vdash e : \tau_2$, with $\tau_1$ bound as a scheme without
  bound variables, then $\Gamma \vdash \lambda x.\, e : \tau_1 \to \tau_2$.
- Let: if $\Gamma \vdash e_1 : \tau_1$ and $\Gamma, x : \mathrm{gen}_\Gamma(\tau_1) \vdash e_2 :
  \tau_2$, then $\Gamma \vdash \mathtt{let}\ x = e_1\ \mathtt{in}\ e_2 : \tau_2$, where
  $\mathrm{gen}_\Gamma(\tau_1)$ binds the type variables of $\tau_1$ that are not free in
  $\Gamma$. -/
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

/-- **More general type scheme.** A scheme $\sigma'$ is more general than a scheme $\sigma$ when
every instance of $\sigma$ is also an instance of $\sigma'$ and every free type variable of
$\sigma'$ is a free type variable of $\sigma$. -/
def Scheme.MoreGeneral (σ' σ : Scheme B) : Prop :=
  (∀ ts, ∃ ts', σ'.inst ts' = σ.inst ts) ∧ σ'.vars ⊆ σ.vars

theorem Scheme.MoreGeneral.refl (σ : Scheme B) : σ.MoreGeneral σ :=
  ⟨fun ts ↦ ⟨ts, rfl⟩, Finset.Subset.refl _⟩

/-- **More general context.** A context $\Gamma'$ is more general than a context $\Gamma$ when the
same names are visible in both and, for each such name $x$, the visible scheme of $x$ in $\Gamma'$
is more general than its visible scheme in $\Gamma$. Only lookups matter, so shadowed bindings
play no role. -/
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

/-- **Contexts with the same lookups are related by generality.** If two typing contexts
$\Gamma'$ and $\Gamma$ give the same lookup result for every name $x$ (the same visible scheme,
or none in both), then $\Gamma'$ is more general than $\Gamma$.

Since the hypothesis is symmetric, $\Gamma$ is then also more general than $\Gamma'$. -/
theorem Ctx.MoreGeneral.of_lookup_eq {Γ' Γ : Ctx B} (h : ∀ x, Γ'.lookup x = Γ.lookup x) :
    Γ'.MoreGeneral Γ :=
  ⟨fun x σ hσ ↦ ⟨σ, (h x).trans hσ, Scheme.MoreGeneral.refl σ⟩,
    fun x σ' hσ' ↦ ⟨σ', (h x).symm.trans hσ', Scheme.MoreGeneral.refl σ'⟩⟩

theorem Ctx.MoreGeneral.refl (Γ : Ctx B) : Γ.MoreGeneral Γ :=
  Ctx.MoreGeneral.of_lookup_eq fun _ ↦ rfl

/-- **Extending more general contexts by a binding.** Let $\Gamma'$ and $\Gamma$ be typing
contexts such that $\Gamma'$ is more general than $\Gamma$, let $x$ be a name, and let $\sigma'$
and $\sigma$ be type schemes such that $\sigma'$ is more general than $\sigma$. Then the context
obtained by putting the binding $x : \sigma'$ in front of $\Gamma'$ is more general than the
context obtained by putting the binding $x : \sigma$ in front of $\Gamma$. -/
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

/-- **Generalizing in a context with fewer free variables.** Let $\Gamma'$ and $\Gamma$ be typing
contexts such that every free type variable of $\Gamma'$ is a free type variable of $\Gamma$, and
let $\tau$ be a monotype. Then the generalization of $\tau$ with respect to $\Gamma'$ is more
general than the generalization of $\tau$ with respect to $\Gamma$. -/
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

/-- **Typing is preserved in more general contexts.** If $\Gamma \vdash e : \tau$ and $\Gamma'$ is
a context more general than $\Gamma$, then $\Gamma' \vdash e : \tau$. -/
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

/-- **Strict upper bound of a finite set of naturals.** For a finite set $S$ of natural numbers,
this is the number $\max S + 1$, where the maximum of the empty set is taken to be $0$. It is
strictly greater than every element of $S$. -/
def above (S : Finset ℕ) : ℕ := S.sup id + 1

theorem lt_above {S : Finset ℕ} {x : ℕ} (hx : x ∈ S) : x < above S :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)

/-- **Renaming step of the substitution lemma.** Let $\Gamma$ be a typing context, $\tau$ a
monotype and $s$ a type substitution. Write $s\Gamma$ for the context obtained by applying $s$ to
every scheme of $\Gamma$, and let $N$ be one more than the largest free type variable of
$s\Gamma$, with $N = 1$ if $s\Gamma$ has none. Let $\rho$ be the substitution sending a type
variable $y$ to $s(y)$ if $y$ is free in $\Gamma$, and to the type variable $y + N$ otherwise.
Then the generalization of $\rho(\tau)$ with respect to $s\Gamma$ is more general than the scheme
obtained by applying $s$ to the free type variables of the generalization of $\tau$ with respect
to $\Gamma$. -/
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

/-- **Hindley–Milner typing is stable under type substitution.** Let $\Gamma$ be a typing
context, $e$ an expression and $\tau$ a monotype with $\Gamma \vdash e : \tau$. Then for every
type substitution $s$, $s\Gamma \vdash e : s\tau$, where $s\Gamma$ applies $s$ to every scheme of
$\Gamma$ and $s\tau$ applies $s$ to $\tau$. -/
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

/-- **Typing inversion for variables.** Let $\Gamma$ be a typing context, $x$ a name and $\tau$ a
monotype. Then $\Gamma \vdash x : \tau$ holds for the variable expression $x$ if and only if
there are a type scheme $\sigma$ and monotypes $(t_i)_{i \in \mathbb{N}}$ such that the lookup of
$x$ in $\Gamma$ gives $\sigma$ and $\tau$ is the instance of $\sigma$ at $(t_i)$. -/
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

/-- **No monotype is an arrow out of itself.** For all monotypes $\tau_1$ and $\tau_2$,
$\tau_1 \ne (\tau_1 \to \tau_2)$. -/
theorem ne_node_self_left (τ₁ τ₂ : Ty B) : τ₁ ≠ node τ₁ τ₂ := fun h ↦ by
  have := congrArg Term.size h
  simp only [Term.size] at this
  omega

/-- **The abstraction $\lambda f.\, f\, f$ has no type.** For every typing context $\Gamma$,
every variable name $f$ and every monotype $\tau$, the judgment
$\Gamma \vdash \lambda f.\, f\, f : \tau$ does not hold.

The λ-bound variable $f$ is monomorphic, so it cannot be applied to itself. -/
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

/-- **`let` generalizes.** For every typing context $\Gamma$, all variable names $f$ and $x$, and
every type variable $\alpha$, the expression $\mathtt{let}\ f = \lambda x.\, x\ \mathtt{in}\ f\, f$
has type $\alpha \to \alpha$ in $\Gamma$. -/
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
