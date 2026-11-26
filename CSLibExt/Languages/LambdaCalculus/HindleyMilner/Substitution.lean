/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.HindleyMilner.Typing
public import Cslib.Foundations.Syntax.HasSubstitution

/-!
# Substitution for let-polymorphic expressions

Free names, binder names, renaming and capture-avoiding substitution on the expressions of
`CSLibExt/Languages/LambdaCalculus/HindleyMilner/Typing.lean`, and the two structural typing
lemmas that substitution needs: weakening along contexts that agree on the free names of an
expression, and the term-substitution lemma for a `let`-bound scheme.

Substitution `e[x := v]` renames a binder `y` of `e` only when `y` is a free name of `v`; under
`Disjoint e.bv v.fv` it never renames, so it is the plain replacement of the free occurrences of
`x`. Every typing result below assumes this disjointness, so no α-renaming typing lemma is
needed.

## Main definitions

- `Expr.fv`, `Expr.bv`, `Expr.names`, `Expr.size`, `Expr.rename`, `Expr.freshName`.
- `Expr.subst`, with the notation `e[x := v]`.

## Main results

- `HasType.fv_subset` : the free names of a typed expression are bound in its context.
- `HasType.mono_fv` : typing transfers to any context whose schemes for the free names of the
  expression are more general, whatever its other bindings and free type variables. The `let`
  case renames the generalized type variables above the free type variables of the new context.
- `HasType.subst_scheme`, `HasType.subst_gen`, `HasType.subst_mono` : term substitution for a
  name bound to a scheme, to a generalized type (`let`), and to a monotype (`λ`).

## References

- F. Pottier, D. Rémy, *The Essence of ML Type Inference*, chapter 10 of B. C. Pierce (ed.),
  *Advanced Topics in Types and Programming Languages*, MIT Press 2005: Lemma 10.5.1.
- H. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, North-Holland 1984, §2.1
  (capture-avoiding substitution).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.HindleyMilner

open Cslib.Unification Cslib.Unification.Term

namespace Expr

/-! ### Names -/

/-- **Free names.** The free names of an expression: a variable $x$ has the free name $x$, an
application has the free names of both sides, $\lambda x.\, e$ has those of $e$ other than $x$,
and $\mathsf{let}\ x = e_1\ \mathsf{in}\ e_2$ has those of $e_1$ and those of $e_2$ other than
$x$. -/
def fv : Expr → Finset String
  | var x => {x}
  | app e₁ e₂ => e₁.fv ∪ e₂.fv
  | lam x e => e.fv.erase x
  | let_ x e₁ e₂ => e₁.fv ∪ e₂.fv.erase x

/-- **Binder names.** The names bound in an expression: the name $x$ of every abstraction
$\lambda x.\, e$ and of every binding $\mathsf{let}\ x = e_1\ \mathsf{in}\ e_2$ occurring in it. -/
def bv : Expr → Finset String
  | var _ => ∅
  | app e₁ e₂ => e₁.bv ∪ e₂.bv
  | lam x e => insert x e.bv
  | let_ x e₁ e₂ => insert x (e₁.bv ∪ e₂.bv)

/-- **Names.** All names occurring in an expression, free or bound. -/
def names : Expr → Finset String
  | var x => {x}
  | app e₁ e₂ => e₁.names ∪ e₂.names
  | lam x e => insert x e.names
  | let_ x e₁ e₂ => insert x (e₁.names ∪ e₂.names)

/-- **Size.** The number of constructors of an expression; names do not count. -/
def size : Expr → ℕ
  | var _ => 1
  | app e₁ e₂ => e₁.size + e₂.size + 1
  | lam _ e => e.size + 1
  | let_ _ e₁ e₂ => e₁.size + e₂.size + 1

/-- **Renaming.** The expression obtained by replacing every occurrence of the name $x$, free or
binding, by the name $y$. -/
def rename (x y : String) : Expr → Expr
  | var z => var (if z = x then y else z)
  | app e₁ e₂ => app (e₁.rename x y) (e₂.rename x y)
  | lam z e => lam (if z = x then y else z) (e.rename x y)
  | let_ z e₁ e₂ => let_ (if z = x then y else z) (e₁.rename x y) (e₂.rename x y)

/-- **Renaming preserves size.** For all names $x$ and $y$ and every expression $e$, renaming
$x$ to $y$ in $e$ does not change its size. -/
theorem size_rename (x y : String) (e : Expr) : (e.rename x y).size = e.size := by
  induction e with
  | var z => rfl
  | app e₁ e₂ ih₁ ih₂ => simp [rename, size, ih₁, ih₂]
  | lam z e ih => simp [rename, size, ih]
  | let_ z e₁ e₂ ih₁ ih₂ => simp [rename, size, ih₁, ih₂]

/-- **A name outside a finite set.** The string of $n + 1$ letters `x`, where $n$ is the
largest length of a string in the finite set $S$ ($0$ if $S$ is empty). It is longer than every
element of $S$, so it does not belong to $S$. -/
def freshName (S : Finset String) : String :=
  String.ofList (List.replicate (S.sup String.length + 1) 'x')

/-- **The fresh name is fresh.** For every finite set $S$ of strings, `freshName S` is not an
element of $S$. -/
theorem freshName_not_mem (S : Finset String) : freshName S ∉ S := by
  intro h
  have := Finset.le_sup (f := String.length) h
  rw [freshName, String.length_ofList, List.length_replicate] at this
  omega

/-! ### Substitution -/

/-- **Capture-avoiding substitution.** The expression $e[x := v]$ obtained from $e$ by replacing
every free occurrence of the name $x$ by the expression $v$:

- a variable $x$ becomes $v$, and any other variable is unchanged;
- an application is substituted on both sides;
- in $\mathsf{let}\ y = e_1\ \mathsf{in}\ e_2$ the bound expression $e_1$ is always
  substituted, even when $y = x$, since $y$ scopes over the body $e_2$ only;
- under a binder $y$ ($\lambda y$, or $\mathsf{let}\ y$ for its body): if $y = x$ the body is
  unchanged; if $y$ is a free name of $v$, the binder is renamed to a name $z$ outside the names
  of the body and of $v$ and outside $\{x, y\}$, then the body is substituted; otherwise the
  body is substituted with the binder kept.

The binder is renamed only when $y$ is free in $v$, so when no binder of $e$ is free in $v$ the
result is the plain replacement of the free occurrences of $x$. -/
def subst (e : Expr) (x : String) (v : Expr) : Expr :=
  match e with
  | var y => if y = x then v else var y
  | app e₁ e₂ => app (e₁.subst x v) (e₂.subst x v)
  | lam y b =>
    if y = x then lam y b
    else if y ∈ v.fv then
      let z := freshName (b.names ∪ v.names ∪ {x, y})
      lam z ((b.rename y z).subst x v)
    else lam y (b.subst x v)
  | let_ y e₁ e₂ =>
    if y = x then let_ y (e₁.subst x v) e₂
    else if y ∈ v.fv then
      let z := freshName (e₂.names ∪ v.names ∪ {x, y})
      let_ z (e₁.subst x v) ((e₂.rename y z).subst x v)
    else let_ y (e₁.subst x v) (e₂.subst x v)
termination_by e.size
decreasing_by all_goals simp only [size, size_rename]; omega

/-- `Expr.subst` gives the notation `e[x := v]`. -/
instance instHasSubstitution : HasSubstitution Expr String Expr where
  subst := subst

variable {e e₁ e₂ v : Expr} {x y : String}

/-- **The notation unfolds to `Expr.subst`.** For all expressions $e$ and $v$ and every name
$x$, $e[x := v]$ is `e.subst x v`. -/
theorem subst_def : e[x := v] = e.subst x v := rfl

/-- **Substitution in a variable.** The variable $y$ becomes $v$ if $y = x$ and stays $y$
otherwise. -/
theorem var_subst : (var y)[x := v] = if y = x then v else var y := by simp [subst_def, subst]

/-- **Substitution in an application.** For all expressions $e_1$, $e_2$, $v$ and every name
$x$, $(e_1\, e_2)[x := v] = (e_1[x := v])\, (e_2[x := v])$: both sides of the application are
substituted. -/
theorem app_subst : (app e₁ e₂)[x := v] = app (e₁[x := v]) (e₂[x := v]) :=
  by simp [subst_def, subst]

/-- **Substitution stops at a binder of the same name.** For all expressions $e$ and $v$ and
every name $x$, $(\lambda x.\, e)[x := v] = \lambda x.\, e$: an abstraction that binds $x$ has no
free occurrence of $x$. -/
theorem lam_subst_self : (lam x e)[x := v] = lam x e := by simp [subst_def, subst]

/-- **Substitution under a binder that is not free in the substituted expression.** If $y \ne x$
and $y$ is not a free name of $v$, then $(\lambda y.\, e)[x := v] = \lambda y.\, e[x := v]$. -/
theorem lam_subst_of_not_mem (hyx : y ≠ x) (hy : y ∉ v.fv) :
    (lam y e)[x := v] = lam y (e[x := v]) := by simp [subst_def, subst, hyx, hy]

/-- **Substitution in a `let` that rebinds the name.** The bound expression is substituted and
the body is unchanged. -/
theorem let_subst_self : (let_ x e₁ e₂)[x := v] = let_ x (e₁[x := v]) e₂ :=
  by simp [subst_def, subst]

/-- **Substitution in a `let` whose name is not free in the substituted expression.** If
$y \ne x$ and $y$ is not a free name of $v$, both the bound expression and the body are
substituted and the binder is kept. -/
theorem let_subst_of_not_mem (hyx : y ≠ x) (hy : y ∉ v.fv) :
    (let_ y e₁ e₂)[x := v] = let_ y (e₁[x := v]) (e₂[x := v]) := by simp [subst_def, subst, hyx, hy]

/-- Renaming keeps the free names, except that the renamed name may become the new one. -/
private theorem fv_rename_subset (y z : String) (e : Expr) :
    (e.rename y z).fv ⊆ e.fv.erase y ∪ {z} := by
  induction e with
  | var w =>
    by_cases hw : w = y
    · simp [rename, fv, hw]
    · simp [rename, fv, hw]
  | app e₁ e₂ ih₁ ih₂ =>
    intro a ha
    simp only [rename, fv, Finset.mem_union] at ha
    rcases ha with ha | ha
    · have := ih₁ ha
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at this ⊢
      simp only [fv, Finset.mem_union]
      tauto
    · have := ih₂ ha
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at this ⊢
      simp only [fv, Finset.mem_union]
      tauto
  | lam w b ih =>
    intro a ha
    simp only [rename, fv, Finset.mem_erase] at ha
    have := ih ha.2
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at this ⊢
    simp only [fv, Finset.mem_erase]
    by_cases hw : w = y
    · simp only [hw, ↓reduceIte] at ha
      subst hw
      tauto
    · simp only [hw, ↓reduceIte] at ha
      tauto
  | let_ w e₁ e₂ ih₁ ih₂ =>
    intro a ha
    simp only [rename, fv, Finset.mem_union, Finset.mem_erase] at ha
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fv]
    rcases ha with ha | ha
    · have := ih₁ ha
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at this
      tauto
    · have := ih₂ ha.2
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at this
      by_cases hw : w = y
      · simp only [hw, ↓reduceIte] at ha
        subst hw
        tauto
      · simp only [hw, ↓reduceIte] at ha
        tauto

/-- **Free names after substitution.** Every free name of $e[x := v]$ is a free name of $e$
other than $x$ or a free name of $v$. -/
theorem fv_subst_subset : (e[x := v]).fv ⊆ e.fv.erase x ∪ v.fv := by
  rw [subst_def]
  induction e using Expr.subst.induct x v with
  | case1 => simp [subst, fv]
  | case2 y hyx => simp [subst, fv, hyx]
  | case3 e₁ e₂ ih₁ ih₂ =>
    intro a ha
    simp only [subst, fv, Finset.mem_union] at ha
    simp only [fv, Finset.mem_union, Finset.mem_erase]
    rcases ha with ha | ha
    · have := ih₁ ha
      simp only [Finset.mem_union, Finset.mem_erase] at this
      tauto
    · have := ih₂ ha
      simp only [Finset.mem_union, Finset.mem_erase] at this
      tauto
  | case4 b =>
    intro a ha
    simp only [subst, ↓reduceIte, fv, Finset.mem_erase] at ha
    simp only [fv, Finset.mem_union, Finset.mem_erase]
    tauto
  | case5 y b hyx hy z ih =>
    intro a ha
    simp only [subst, hyx, hy, ↓reduceIte, fv, Finset.mem_erase] at ha
    have h1 := ih ha.2
    simp only [Finset.mem_union, Finset.mem_erase] at h1
    simp only [fv, Finset.mem_union, Finset.mem_erase]
    rcases h1 with ⟨h1, h2⟩ | h1
    · have h3 := fv_rename_subset y _ b h2
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at h3
      tauto
    · tauto
  | case6 y b hyx hy ih =>
    intro a ha
    simp only [subst, hyx, hy, ↓reduceIte, fv, Finset.mem_erase] at ha
    have h1 := ih ha.2
    simp only [Finset.mem_union, Finset.mem_erase] at h1
    simp only [fv, Finset.mem_union, Finset.mem_erase]
    tauto
  | case7 e₁ e₂ ih₁ =>
    intro a ha
    simp only [subst, ↓reduceIte, fv, Finset.mem_union, Finset.mem_erase] at ha
    simp only [fv, Finset.mem_union, Finset.mem_erase]
    rcases ha with ha | ha
    · have := ih₁ ha
      simp only [Finset.mem_union, Finset.mem_erase] at this
      tauto
    · tauto
  | case8 y e₁ e₂ hyx hy z ih₁ ih₂ =>
    intro a ha
    simp only [subst, hyx, hy, ↓reduceIte, fv, Finset.mem_union, Finset.mem_erase] at ha
    simp only [fv, Finset.mem_union, Finset.mem_erase]
    rcases ha with ha | ha
    · have := ih₁ ha
      simp only [Finset.mem_union, Finset.mem_erase] at this
      tauto
    · have h1 := ih₂ ha.2
      simp only [Finset.mem_union, Finset.mem_erase] at h1
      rcases h1 with ⟨h1, h2⟩ | h1
      · have h3 := fv_rename_subset y _ e₂ h2
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at h3
        tauto
      · tauto
  | case9 y e₁ e₂ hyx hy ih₁ ih₂ =>
    intro a ha
    simp only [subst, hyx, hy, ↓reduceIte, fv, Finset.mem_union, Finset.mem_erase] at ha
    simp only [fv, Finset.mem_union, Finset.mem_erase]
    rcases ha with ha | ha
    · have := ih₁ ha
      simp only [Finset.mem_union, Finset.mem_erase] at this
      tauto
    · have h1 := ih₂ ha.2
      simp only [Finset.mem_union, Finset.mem_erase] at h1
      tauto

/-- **Binder names after substitution.** If no binder name of $e$ is a free name of $v$, every
binder name of $e[x := v]$ is a binder name of $e$ or of $v$. -/
theorem bv_subst_subset (h : Disjoint e.bv v.fv) : (e[x := v]).bv ⊆ e.bv ∪ v.bv := by
  induction e with
  | var y =>
    rw [var_subst]
    split_ifs <;> simp [bv]
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [bv, Finset.disjoint_union_left] at h
    rw [app_subst]
    intro a ha
    simp only [bv, Finset.mem_union] at ha ⊢
    rcases ha with ha | ha
    · have := ih₁ h.1 ha
      simp only [Finset.mem_union] at this
      tauto
    · have := ih₂ h.2 ha
      simp only [Finset.mem_union] at this
      tauto
  | lam y b ih =>
    have hy : y ∉ v.fv := Finset.disjoint_left.mp h (by simp [bv])
    have hb : Disjoint b.bv v.fv := Finset.disjoint_of_subset_left (by simp [bv]) h
    by_cases hyx : y = x
    · subst hyx
      rw [lam_subst_self]
      exact Finset.subset_union_left
    · rw [lam_subst_of_not_mem hyx hy]
      intro a ha
      simp only [bv, Finset.mem_insert, Finset.mem_union] at ha ⊢
      rcases ha with ha | ha
      · tauto
      · have := ih hb ha
        simp only [Finset.mem_union] at this
        tauto
  | let_ y e₁ e₂ ih₁ ih₂ =>
    have hy : y ∉ v.fv := Finset.disjoint_left.mp h (by simp [bv])
    have h₁ : Disjoint e₁.bv v.fv := Finset.disjoint_of_subset_left (by
      intro a ha; simp [bv, ha]) h
    have h₂ : Disjoint e₂.bv v.fv := Finset.disjoint_of_subset_left (by
      intro a ha; simp [bv, ha]) h
    by_cases hyx : y = x
    · subst hyx
      rw [let_subst_self]
      intro a ha
      simp only [bv, Finset.mem_insert, Finset.mem_union] at ha ⊢
      rcases ha with ha | ha | ha
      · tauto
      · have := ih₁ h₁ ha
        simp only [Finset.mem_union] at this
        tauto
      · tauto
    · rw [let_subst_of_not_mem hyx hy]
      intro a ha
      simp only [bv, Finset.mem_insert, Finset.mem_union] at ha ⊢
      rcases ha with ha | ha | ha
      · tauto
      · have := ih₁ h₁ ha
        simp only [Finset.mem_union] at this
        tauto
      · have := ih₂ h₂ ha
        simp only [Finset.mem_union] at this
        tauto

end Expr

/-! ### Structural typing lemmas -/

variable {B : Type u}

open Expr

/-- **Free names of a typed expression are bound.** If $\Gamma \vdash e : \tau$, then every free
name of $e$ has a scheme in $\Gamma$. -/
theorem HasType.fv_subset {Γ : Ctx B} {e : Expr} {τ : Ty B} (h : HasType Γ e τ) :
    ∀ y ∈ e.fv, (Γ.lookup y).isSome := by
  induction h with
  | var ts hx =>
    intro y hy
    simp only [fv, Finset.mem_singleton] at hy
    subst hy
    simp [hx]
  | app _ _ ih₁ ih₂ =>
    intro y hy
    simp only [fv, Finset.mem_union] at hy
    rcases hy with hy | hy
    exacts [ih₁ y hy, ih₂ y hy]
  | @lam Γ x e τ₁ τ₂ _ ih =>
    intro y hy
    simp only [fv, Finset.mem_erase] at hy
    have := ih y hy.2
    simpa only [Ctx.lookup_cons, hy.1, ↓reduceIte] using this
  | @let_ Γ x e₁ e₂ τ₁ τ₂ _ _ ih₁ ih₂ =>
    intro y hy
    simp only [fv, Finset.mem_union, Finset.mem_erase] at hy
    rcases hy with hy | hy
    · exact ih₁ y hy
    · have := ih₂ y hy.2
      simpa only [Ctx.lookup_cons, hy.1, ↓reduceIte] using this

/-- A type substitution that fixes the free type variables of a context fixes its lookups. -/
private theorem lookup_subst_of_eq_var {Γ : Ctx B} {s : Subst B}
    (h : ∀ y ∈ Γ.ftv, s y = Term.var y) (x : String) : (Γ.subst s).lookup x = Γ.lookup x := by
  rw [Ctx.lookup_subst_congr (t := Term.var) h, Ctx.lookup_subst]
  cases Γ.lookup x with
  | none => rfl
  | some σ =>
    simp only [Option.map_some, Option.some.injEq]
    have : σ.substTy Term.var = σ.subst Term.var := by
      rw [Scheme.substTy]
      congr 1
    rw [this, subst_id]

/-- Generalizing in another context after renaming the generalized type variables above the free
type variables of both contexts gives a more general scheme. -/
private theorem gen_rename_moreGeneral (Γ Γ' : Ctx B) (τ : Ty B) :
    (gen Γ' (τ.subst fun y ↦
        if y ∈ Γ.ftv then Term.var y else Term.var (y + above (Γ.ftv ∪ Γ'.ftv)))).MoreGeneral
      (gen Γ τ) := by
  set N := above (Γ.ftv ∪ Γ'.ftv)
  refine ⟨fun ts ↦ ⟨fun z ↦ if N ≤ z then ts (z - N) else Term.var z, ?_⟩, ?_⟩
  · rw [inst_gen, inst_gen, subst_subst]
    refine subst_congr fun y _ ↦ ?_
    by_cases hy : y ∈ Γ.ftv
    · have hyN : y < N := lt_above (Finset.mem_union_left _ hy)
      by_cases hy' : y ∈ Γ'.ftv
      · simp [hy, hy']
      · simp [hy, hy', show ¬ N ≤ y by omega]
    · have hN : y + N ∉ Γ'.ftv := fun h ↦
        absurd (lt_above (Finset.mem_union_right Γ.ftv h)) (by omega)
      simp [hy, hN]
  · intro z hz
    rw [vars_gen, Finset.mem_filter] at hz ⊢
    obtain ⟨hz₁, hz₂⟩ := hz
    obtain ⟨y, hy, hzy⟩ := exists_of_mem_vars_subst hz₁
    by_cases hyΓ : y ∈ Γ.ftv
    · simp only [hyΓ, ↓reduceIte, Term.vars, Finset.mem_singleton] at hzy
      subst hzy
      exact ⟨hy, hyΓ⟩
    · simp only [hyΓ, ↓reduceIte, Term.vars, Finset.mem_singleton] at hzy
      subst hzy
      exact absurd (lt_above (Finset.mem_union_right Γ.ftv hz₂)) (by omega)

/-- **Weakening for let-polymorphic typing.** Let $\Gamma \vdash e : \tau$, and let $\Gamma'$ be
a context in which every free name $y$ of $e$ that has a scheme $\sigma$ in $\Gamma$ has a scheme
in $\Gamma'$ more general than $\sigma$. Then $\Gamma' \vdash e : \tau$. The context $\Gamma'$
may bind other names and have other free type variables; at each `let` of $e$, the type
variables generalized in $\Gamma$ are renamed above the free type variables of $\Gamma'$. -/
theorem HasType.mono_fv {Γ : Ctx B} {e : Expr} {τ : Ty B} (h : HasType Γ e τ) {Γ' : Ctx B}
    (hΓ : ∀ y ∈ e.fv, ∀ σ, Γ.lookup y = some σ →
      ∃ σ', Γ'.lookup y = some σ' ∧ σ'.MoreGeneral σ) :
    HasType Γ' e τ := by
  induction e generalizing Γ Γ' τ with
  | var x =>
    obtain ⟨σ, ts, hx, rfl⟩ := hasType_var_iff.mp h
    obtain ⟨σ', hσ', hg⟩ := hΓ x (by simp [fv]) σ hx
    obtain ⟨ts', hts'⟩ := hg.1 ts
    rw [← hts']
    exact HasType.var ts' hσ'
  | app e₁ e₂ ih₁ ih₂ =>
    obtain ⟨τ₁, h₁, h₂⟩ := hasType_app_iff.mp h
    exact HasType.app (ih₁ h₁ fun y hy ↦ hΓ y (by simp [fv, hy]))
      (ih₂ h₂ fun y hy ↦ hΓ y (by simp [fv, hy]))
  | lam x e ih =>
    obtain ⟨τ₁, τ₂, rfl, hb⟩ := hasType_lam_iff.mp h
    refine HasType.lam (ih hb fun y hy σ hσ ↦ ?_)
    by_cases hyx : y = x
    · subst hyx
      simp only [Ctx.lookup_cons, ↓reduceIte] at hσ ⊢
      exact ⟨σ, hσ, Scheme.MoreGeneral.refl σ⟩
    · simp only [Ctx.lookup_cons, hyx, ↓reduceIte] at hσ ⊢
      exact hΓ y (by simp [fv, hy, hyx]) σ hσ
  | let_ x e₁ e₂ ih₁ ih₂ =>
    obtain ⟨τ₁, h₁, h₂⟩ := hasType_let_iff.mp h
    let ρ : Subst B := fun y ↦
      if y ∈ Γ.ftv then Term.var y else Term.var (y + above (Γ.ftv ∪ Γ'.ftv))
    have h₁' : HasType Γ e₁ (τ₁.subst ρ) :=
      (h₁.subst ρ).mono (Ctx.MoreGeneral.of_lookup_eq fun z ↦
        (lookup_subst_of_eq_var (fun y hy ↦ by simp only [ρ, hy, ↓reduceIte]) z).symm)
    refine HasType.let_ (ih₁ h₁' fun y hy ↦ hΓ y (by simp [fv, hy])) (ih₂ h₂ fun y hy σ hσ ↦ ?_)
    by_cases hyx : y = x
    · subst hyx
      simp only [Ctx.lookup_cons, ↓reduceIte, Option.some.injEq] at hσ ⊢
      subst hσ
      exact ⟨_, rfl, gen_rename_moreGeneral Γ Γ' τ₁⟩
    · simp only [Ctx.lookup_cons, hyx, ↓reduceIte] at hσ ⊢
      exact hΓ y (by simp [fv, hy, hyx]) σ hσ

/-- **Binding a name that is not free.** If $\Gamma \vdash e : \tau$ and $y$ is not a free name
of $e$, then $e$ has type $\tau$ in $\Gamma$ extended in front by $y : \sigma$, for every scheme
$\sigma$. -/
theorem HasType.weaken_cons {Γ : Ctx B} {e : Expr} {τ : Ty B} (h : HasType Γ e τ) {y : String}
    (hy : y ∉ e.fv) (σ : Scheme B) : HasType ((y, σ) :: Γ) e τ :=
  h.mono_fv fun z hz ρ hρ ↦ ⟨ρ, by
    have hzy : z ≠ y := fun h ↦ hy (h ▸ hz)
    simpa only [Ctx.lookup_cons, hzy, ↓reduceIte] using hρ, Scheme.MoreGeneral.refl ρ⟩

/-- Exchanging two bindings of different names keeps every lookup. -/
private theorem lookup_swap {Γ : Ctx B} {x y : String} (hxy : x ≠ y) (σ ρ : Scheme B)
    (z : String) : Ctx.lookup ((x, σ) :: (y, ρ) :: Γ) z = Ctx.lookup ((y, ρ) :: (x, σ) :: Γ) z := by
  simp only [Ctx.lookup_cons]
  by_cases hzx : z = x
  · subst hzx
    simp [hxy]
  · simp [hzx]

/-- A binding shadowed by a binding of the same name plays no role in lookups. -/
private theorem lookup_shadow {Γ : Ctx B} {x : String} (σ ρ : Scheme B) (z : String) :
    Ctx.lookup ((x, σ) :: (x, ρ) :: Γ) z = Ctx.lookup ((x, σ) :: Γ) z := by
  simp only [Ctx.lookup_cons]
  by_cases hzx : z = x <;> simp [hzx]

/-- Binding a name that the context does not bind keeps its free type variables. -/
private theorem ftv_subset_ftv_cons {Γ : Ctx B} {x : String} (hx : Γ.lookup x = none)
    (σ : Scheme B) : Γ.ftv ⊆ Ctx.ftv ((x, σ) :: Γ) := by
  intro z hz
  obtain ⟨y, ρ, hy, hz⟩ := Ctx.mem_ftv.mp hz
  have hyx : y ≠ x := by
    rintro rfl
    rw [hx] at hy
    cases hy
  exact Ctx.mem_ftv.mpr ⟨y, ρ, by simpa only [Ctx.lookup_cons, hyx, ↓reduceIte] using hy, hz⟩

/-- Typing transfers to a context with the same lookups. -/
private theorem HasType.of_lookup_eq {Γ Γ' : Ctx B} {e : Expr} {τ : Ty B} (h : HasType Γ e τ)
    (hΓ : ∀ z, Γ'.lookup z = Γ.lookup z) : HasType Γ' e τ :=
  h.mono (Ctx.MoreGeneral.of_lookup_eq hΓ)

/-- **Term substitution for a scheme.** Let $\Gamma$ be a context that does not bind the name
$x$, let $\sigma$ be a scheme such that $\Gamma \vdash v : \tau'$ for every instance $\tau'$ of
$\sigma$, and let $\Gamma, x : \sigma \vdash e : \tau$, where no binder name of $e$ is a free
name of $v$. Then $\Gamma \vdash e[x := v] : \tau$. -/
theorem HasType.subst_scheme {Γ : Ctx B} {x : String} {σ : Scheme B} {e v : Expr} {τ : Ty B}
    (hx : Γ.lookup x = none) (hv : ∀ ts, HasType Γ v (σ.inst ts))
    (he : HasType ((x, σ) :: Γ) e τ) (hd : Disjoint e.bv v.fv) :
    HasType Γ (e[x := v]) τ := by
  induction e generalizing Γ τ with
  | var y =>
    rw [var_subst]
    obtain ⟨σ₀, ts, hy, rfl⟩ := hasType_var_iff.mp he
    by_cases hyx : y = x
    · subst hyx
      simp only [Ctx.lookup_cons, ↓reduceIte, Option.some.injEq] at hy
      subst hy
      simpa using hv ts
    · simp only [Ctx.lookup_cons, hyx, ↓reduceIte] at hy ⊢
      exact HasType.var ts hy
  | app e₁ e₂ ih₁ ih₂ =>
    rw [app_subst]
    obtain ⟨τ₁, h₁, h₂⟩ := hasType_app_iff.mp he
    simp only [bv, Finset.disjoint_union_left] at hd
    exact HasType.app (ih₁ hx hv h₁ hd.1) (ih₂ hx hv h₂ hd.2)
  | lam y b ih =>
    obtain ⟨τ₁, τ₂, rfl, hb⟩ := hasType_lam_iff.mp he
    by_cases hyx : y = x
    · subst hyx
      rw [lam_subst_self]
      exact HasType.lam (hb.of_lookup_eq fun z ↦ (lookup_shadow _ _ z).symm)
    · have hyv : y ∉ v.fv := Finset.disjoint_left.mp hd (by simp [bv])
      rw [lam_subst_of_not_mem hyx hyv]
      have hxy : x ≠ y := Ne.symm hyx
      refine HasType.lam (ih ?_ (fun ts ↦ (hv ts).weaken_cons hyv _) ?_
        (Finset.disjoint_of_subset_left (by simp [bv]) hd))
      · simpa only [Ctx.lookup_cons, hxy, ↓reduceIte] using hx
      · exact hb.of_lookup_eq fun z ↦ lookup_swap hxy _ _ z
  | let_ y e₁ e₂ ih₁ ih₂ =>
    obtain ⟨τ₁, h₁, h₂⟩ := hasType_let_iff.mp he
    have hd₁ : Disjoint e₁.bv v.fv := Finset.disjoint_of_subset_left (by
      intro a ha; simp [bv, ha]) hd
    have hd₂ : Disjoint e₂.bv v.fv := Finset.disjoint_of_subset_left (by
      intro a ha; simp [bv, ha]) hd
    have hgen : (gen Γ τ₁).MoreGeneral (gen ((x, σ) :: Γ) τ₁) :=
      gen_moreGeneral (ftv_subset_ftv_cons hx σ) τ₁
    by_cases hyx : y = x
    · subst hyx
      rw [let_subst_self]
      refine HasType.let_ (ih₁ hx hv h₁ hd₁) (h₂.mono_fv fun z _ ρ hρ ↦ ?_)
      by_cases hzy : z = y
      · subst hzy
        simp only [Ctx.lookup_cons, ↓reduceIte, Option.some.injEq] at hρ ⊢
        subst hρ
        exact ⟨_, rfl, hgen⟩
      · simp only [Ctx.lookup_cons, hzy, ↓reduceIte] at hρ ⊢
        exact ⟨ρ, hρ, Scheme.MoreGeneral.refl ρ⟩
    · have hyv : y ∉ v.fv := Finset.disjoint_left.mp hd (by simp [bv])
      rw [let_subst_of_not_mem hyx hyv]
      have hxy : x ≠ y := Ne.symm hyx
      refine HasType.let_ (ih₁ hx hv h₁ hd₁) ?_
      have h₂' : HasType ((y, gen ((x, σ) :: Γ) τ₁) :: Γ) (e₂[x := v]) τ :=
        ih₂ (by simpa only [Ctx.lookup_cons, hxy, ↓reduceIte] using hx)
          (fun ts ↦ (hv ts).weaken_cons hyv _)
          (h₂.of_lookup_eq fun z ↦ lookup_swap hxy _ _ z) hd₂
      refine h₂'.mono_fv fun z _ ρ hρ ↦ ?_
      by_cases hzy : z = y
      · subst hzy
        simp only [Ctx.lookup_cons, ↓reduceIte, Option.some.injEq] at hρ ⊢
        subst hρ
        exact ⟨_, rfl, hgen⟩
      · simp only [Ctx.lookup_cons, hzy, ↓reduceIte] at hρ ⊢
        exact ⟨ρ, hρ, Scheme.MoreGeneral.refl ρ⟩

/-- **Term substitution for a `let`-bound name.** Let $\Gamma$ be a context that does not bind
the name $x$, with $\Gamma \vdash v : \tau_1$ and $\Gamma, x : \mathrm{gen}_\Gamma(\tau_1) \vdash
e : \tau$, where no binder name of $e$ is a free name of $v$. Then
$\Gamma \vdash e[x := v] : \tau$. -/
theorem HasType.subst_gen {Γ : Ctx B} {x : String} {e v : Expr} {τ₁ τ : Ty B}
    (hx : Γ.lookup x = none) (hv : HasType Γ v τ₁) (he : HasType ((x, gen Γ τ₁) :: Γ) e τ)
    (hd : Disjoint e.bv v.fv) : HasType Γ (e[x := v]) τ := by
  refine HasType.subst_scheme hx (fun ts ↦ ?_) he hd
  rw [inst_gen]
  exact (hv.subst _).of_lookup_eq fun z ↦
    (lookup_subst_of_eq_var (fun y hy ↦ by simp only [hy, ↓reduceIte]) z).symm

/-- **Term substitution for a `λ`-bound name.** Let $\Gamma$ be a context that does not bind the
name $x$, with $\Gamma \vdash v : \tau_1$ and $\Gamma, x : \tau_1 \vdash e : \tau$, where no
binder name of $e$ is a free name of $v$. Then $\Gamma \vdash e[x := v] : \tau$. -/
theorem HasType.subst_mono {Γ : Ctx B} {x : String} {e v : Expr} {τ₁ τ : Ty B}
    (hx : Γ.lookup x = none) (hv : HasType Γ v τ₁)
    (he : HasType ((x, toScheme τ₁) :: Γ) e τ) (hd : Disjoint e.bv v.fv) :
    HasType Γ (e[x := v]) τ :=
  HasType.subst_scheme hx (fun ts ↦ by rw [inst_toScheme]; exact hv) he hd

end Cslib.HindleyMilner
