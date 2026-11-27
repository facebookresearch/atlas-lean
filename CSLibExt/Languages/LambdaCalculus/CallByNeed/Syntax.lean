/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Image

/-!
# Call-by-need: syntax

Expressions of Launchbury's language for lazy evaluation: variables, abstractions,
applications of an expression to a variable, recursive `let` with any number of bindings,
numerals and addition. Arguments of applications are variables, so an argument is shared by
binding it in the heap, not copied. The bindings of a `let` form their own inductive type,
mutual with expressions.

The operations are the free names `Expr.fv`, all names `Expr.names`, naive simultaneous
substitution of names for free names `Expr.subst`, renaming of every occurrence `Expr.map`,
and the values `Expr.IsValue` (abstractions and numerals). Each operation on expressions has a
twin on bindings.

## Source and representation

The syntax is that of Launchbury [Lau93, §3.1], with the numerals and addition of
[Lau93, §4]; values are as in [Lau93, §3.2]. Names are elements of any type `V` with decidable
equality, and terms are named, not locally nameless. The normalization of [Lau93, §3.1] is not
formalized: arguments are variables by construction, and bound variables need not be distinct.
The source semantics assumes an inexhaustible supply of fresh names. Over a finite type of names
the `let` rule of the semantics can run out of them, and the `let` then has no evaluation, as an
allocation failure: over `Unit`, where `x` is the only name, `let x = 7 in x` has none.

Substitution is the naive simultaneous substitution of Sestoft [Ses97, §2.1]: a list of pairs
`(x, p)` replaces each free occurrence of a name `x` by the name `p`, a binder removes its own
names from the list, and binders are never renamed, so a substituted name that lands under a
binder of the same name is captured. Sestoft calls a configuration good for a set of names to
avoid when, among other conditions, none of its bound names is to be avoided or bound in the heap
[Ses97, §2.5, Definition 1]; a closed expression in the empty heap, with no names to avoid, is
good, and its evaluation involves no capture [Ses97, §2.5, Proposition 1]. The judgement `Eval`
of the semantics places no such condition on its configurations: from a configuration in which a
bound name of the expression is also bound in the heap, its substitutions can capture. Absence
of capture is not proved here. `Expr.map` applies a function to every occurrence of a name,
binders included; for a permutation it is a renaming.

## References

* [Lau93] J. Launchbury, *A natural semantics for lazy evaluation*, POPL 1993, pp. 144–154.
* [Ses97] P. Sestoft, *Deriving a lazy abstract machine*, Journal of Functional Programming
  7(3), 1997.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.CallByNeed

universe u

mutual

/-- Expressions: variables, abstractions, applications to a variable, recursive `let`,
numerals and addition. -/
inductive Expr (V : Type u) : Type u where
  /-- A variable. -/
  | var : V → Expr V
  /-- The abstraction `λx. e`. -/
  | lam : V → Expr V → Expr V
  /-- The application `e x` of an expression to a variable. -/
  | app : Expr V → V → Expr V
  /-- The recursive `let x₁ = e₁, …, xₙ = eₙ in e`; every `xᵢ` scopes over every `eⱼ` and
  over `e`. -/
  | letrec : Binds V → Expr V → Expr V
  /-- A numeral. -/
  | num : ℕ → Expr V
  /-- The addition `e₁ + e₂`. -/
  | add : Expr V → Expr V → Expr V

/-- The bindings `x₁ = e₁, …, xₙ = eₙ` of a `let`. -/
inductive Binds (V : Type u) : Type u where
  /-- No binding. -/
  | nil : Binds V
  /-- The binding `x = e` followed by more bindings. -/
  | cons : V → Expr V → Binds V → Binds V

end

deriving instance DecidableEq for Expr, Binds

/-- The names bound by the bindings, in order. -/
def Binds.vars {V : Type u} : Binds V → List V
  | .nil => []
  | .cons x _ bs => x :: bs.vars

/-- The right-hand sides of the bindings, in order. -/
def Binds.exprs {V : Type u} : Binds V → List (Expr V)
  | .nil => []
  | .cons _ e bs => e :: bs.exprs

mutual

/-- The free names of an expression. The names bound by a `let` are not free in it,
in its right-hand sides or in its body. -/
def Expr.fv {V : Type u} [DecidableEq V] : Expr V → Finset V
  | .var x => {x}
  | .lam x e => e.fv.erase x
  | .app e x => insert x e.fv
  | .letrec bs e => (bs.fv ∪ e.fv) \ bs.vars.toFinset
  | .num _ => ∅
  | .add e₁ e₂ => e₁.fv ∪ e₂.fv

/-- The free names of the right-hand sides of bindings; the names the bindings bind are not
removed. -/
def Binds.fv {V : Type u} [DecidableEq V] : Binds V → Finset V
  | .nil => ∅
  | .cons _ e bs => e.fv ∪ bs.fv

end

mutual

/-- Every name occurring in an expression, bound or free. -/
def Expr.names {V : Type u} [DecidableEq V] : Expr V → Finset V
  | .var x => {x}
  | .lam x e => insert x e.names
  | .app e x => insert x e.names
  | .letrec bs e => bs.names ∪ e.names
  | .num _ => ∅
  | .add e₁ e₂ => e₁.names ∪ e₂.names

/-- Every name occurring in bindings: the bound names and the names of the right-hand
sides. -/
def Binds.names {V : Type u} [DecidableEq V] : Binds V → Finset V
  | .nil => ∅
  | .cons x e bs => insert x (e.names ∪ bs.names)

end

mutual

/-- Naive simultaneous substitution: each free occurrence of a name `x` that is a key of the
list `σ` is replaced by the value of the first pair with key `x`. A binder removes its names
from the list, and binders are never renamed. -/
def Expr.subst {V : Type u} [DecidableEq V] (σ : List (V × V)) : Expr V → Expr V
  | .var x => .var ((σ.lookup x).getD x)
  | .lam x e => .lam x (e.subst (σ.filter fun q => q.1 ≠ x))
  | .app e x => .app (e.subst σ) ((σ.lookup x).getD x)
  | .letrec bs e =>
      .letrec (bs.subst (σ.filter fun q => q.1 ∉ bs.vars))
        (e.subst (σ.filter fun q => q.1 ∉ bs.vars))
  | .num k => .num k
  | .add e₁ e₂ => .add (e₁.subst σ) (e₂.subst σ)

/-- Substitution in the right-hand sides of bindings; the bound names are kept and are not
removed from the list. -/
def Binds.subst {V : Type u} [DecidableEq V] (σ : List (V × V)) : Binds V → Binds V
  | .nil => .nil
  | .cons x e bs => .cons x (e.subst σ) (bs.subst σ)

end

mutual

/-- Apply `f` to every occurrence of a name, binders included. -/
def Expr.map {V : Type u} (f : V → V) : Expr V → Expr V
  | .var x => .var (f x)
  | .lam x e => .lam (f x) (e.map f)
  | .app e x => .app (e.map f) (f x)
  | .letrec bs e => .letrec (bs.map f) (e.map f)
  | .num k => .num k
  | .add e₁ e₂ => .add (e₁.map f) (e₂.map f)

/-- Apply `f` to every occurrence of a name in bindings, bound names included. -/
def Binds.map {V : Type u} (f : V → V) : Binds V → Binds V
  | .nil => .nil
  | .cons x e bs => .cons (f x) (e.map f) (bs.map f)

end

/-- Values: abstractions and numerals. -/
inductive Expr.IsValue {V : Type u} : Expr V → Prop
  /-- An abstraction is a value. -/
  | lam (x : V) (e : Expr V) : Expr.IsValue (.lam x e)
  /-- A numeral is a value. -/
  | num (k : ℕ) : Expr.IsValue (.num k)

/-! ### Supporting lemmas -/

/-- The name a substitution list gives `x` is `x` itself when `x` is not a key, and a value of the
list otherwise. -/
private theorem lookup_getD_cases {V : Type u} [DecidableEq V] (σ : List (V × V)) (x : V) :
    ((σ.lookup x).getD x = x ∧ x ∉ σ.map Prod.fst) ∨ (σ.lookup x).getD x ∈ σ.map Prod.snd := by
  induction σ with
  | nil => simp
  | cons q σ ih =>
    obtain ⟨k, p⟩ := q
    rw [List.lookup_cons]
    by_cases hxk : x = k
    · subst hxk
      simp
    · have hb : (x == k) = false := by simpa using hxk
      rw [hb]
      rcases ih with ⟨h₁, h₂⟩ | h
      · exact Or.inl ⟨h₁, by simp [hxk, h₂]⟩
      · exact Or.inr (by simp [h])

/-- A key of a filtered substitution list is a key of the list. -/
private theorem mem_keys_of_mem_keys_filter {V : Type u} {σ : List (V × V)} {P : V × V → Bool}
    {y : V} (h : y ∈ (σ.filter P).map Prod.fst) : y ∈ σ.map Prod.fst := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨q, (List.mem_filter.mp hq).1, rfl⟩

/-- A value of a filtered substitution list is a value of the list. -/
private theorem mem_vals_of_mem_vals_filter {V : Type u} {σ : List (V × V)} {P : V × V → Bool}
    {y : V} (h : y ∈ (σ.filter P).map Prod.snd) : y ∈ σ.map Prod.snd := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨q, (List.mem_filter.mp hq).1, rfl⟩

/-- A key of a substitution list that the filter keeps is a key of the filtered list. -/
private theorem mem_keys_filter {V : Type u} {σ : List (V × V)} {P : V → Bool} {y : V}
    (h : y ∈ σ.map Prod.fst) (hy : P y = true) :
    y ∈ (σ.filter fun q => P q.1).map Prod.fst := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, hy⟩, rfl⟩

/-- Substitution keeps the names bound by bindings. -/
private theorem vars_subst {V : Type u} [DecidableEq V] (σ : List (V × V)) :
    ∀ bs : Binds V, (bs.subst σ).vars = bs.vars
  | .nil => rfl
  | .cons x e bs => by rw [Binds.subst, Binds.vars, Binds.vars, vars_subst σ bs]

/-- A name is free in bindings exactly when it is free in one of their right-hand sides. -/
private theorem mem_binds_fv {V : Type u} [DecidableEq V] {y : V} :
    ∀ bs : Binds V, y ∈ bs.fv ↔ ∃ e ∈ bs.exprs, y ∈ e.fv
  | .nil => by simp [Binds.fv, Binds.exprs]
  | .cons x e bs => by simp [Binds.fv, Binds.exprs, mem_binds_fv bs]

mutual

/-- Free names of a substitution instance of an expression (both twins at once). -/
private theorem fv_subst_e {V : Type u} [DecidableEq V] :
    ∀ (σ : List (V × V)) (e : Expr V), ∀ y ∈ (e.subst σ).fv,
      (y ∈ e.fv ∧ y ∉ σ.map Prod.fst) ∨ y ∈ σ.map Prod.snd
  | σ, .var x => by
    intro y hy
    simp only [Expr.subst, Expr.fv, Finset.mem_singleton] at hy
    subst hy
    rcases lookup_getD_cases σ x with ⟨h₁, h₂⟩ | h
    · rw [h₁]
      exact Or.inl ⟨by simp [Expr.fv], h₂⟩
    · exact Or.inr h
  | σ, .lam x e => by
    intro y hy
    simp only [Expr.subst, Expr.fv, Finset.mem_erase] at hy
    obtain ⟨hyx, hy⟩ := hy
    rcases fv_subst_e (σ.filter fun q => q.1 ≠ x) e y hy with ⟨hfv, hk⟩ | hv
    · refine Or.inl ⟨by simp [Expr.fv, hyx, hfv], fun hk' => hk ?_⟩
      exact mem_keys_filter (P := fun z => decide (z ≠ x)) hk' (by simpa using hyx)
    · exact Or.inr (mem_vals_of_mem_vals_filter hv)
  | σ, .app e x => by
    intro y hy
    simp only [Expr.subst, Expr.fv, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · rcases lookup_getD_cases σ x with ⟨h₁, h₂⟩ | h
      · rw [h₁]
        exact Or.inl ⟨by simp [Expr.fv], h₂⟩
      · exact Or.inr h
    · rcases fv_subst_e σ e y hy with ⟨hfv, hk⟩ | hv
      · exact Or.inl ⟨by simp [Expr.fv, hfv], hk⟩
      · exact Or.inr hv
  | σ, .letrec bs e => by
    intro y hy
    simp only [Expr.subst, Expr.fv, Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset,
      vars_subst] at hy
    obtain ⟨hy, hyv⟩ := hy
    have key : ∀ z, (z ∈ bs.fv ∨ z ∈ e.fv) → z ∉ bs.vars →
        z ∉ (σ.filter fun q => q.1 ∉ bs.vars).map Prod.fst →
        (z ∈ (Expr.letrec bs e).fv ∧ z ∉ σ.map Prod.fst) := by
      intro z hz hzv hk
      refine ⟨by simp [Expr.fv, hz, hzv], fun hk' => hk ?_⟩
      exact mem_keys_filter (P := fun w => decide (w ∉ bs.vars)) hk' (by simpa using hzv)
    rcases hy with hy | hy
    · rcases fv_subst_b (σ.filter fun q => q.1 ∉ bs.vars) bs y hy with ⟨hfv, hk⟩ | hv
      · exact Or.inl (key y (Or.inl hfv) hyv hk)
      · exact Or.inr (mem_vals_of_mem_vals_filter hv)
    · rcases fv_subst_e (σ.filter fun q => q.1 ∉ bs.vars) e y hy with ⟨hfv, hk⟩ | hv
      · exact Or.inl (key y (Or.inr hfv) hyv hk)
      · exact Or.inr (mem_vals_of_mem_vals_filter hv)
  | σ, .num k => by simp [Expr.subst, Expr.fv]
  | σ, .add e₁ e₂ => by
    intro y hy
    simp only [Expr.subst, Expr.fv, Finset.mem_union] at hy
    rcases hy with hy | hy
    · rcases fv_subst_e σ e₁ y hy with ⟨hfv, hk⟩ | hv
      · exact Or.inl ⟨by simp [Expr.fv, hfv], hk⟩
      · exact Or.inr hv
    · rcases fv_subst_e σ e₂ y hy with ⟨hfv, hk⟩ | hv
      · exact Or.inl ⟨by simp [Expr.fv, hfv], hk⟩
      · exact Or.inr hv

/-- Free names of a substitution instance of bindings. -/
private theorem fv_subst_b {V : Type u} [DecidableEq V] :
    ∀ (σ : List (V × V)) (bs : Binds V), ∀ y ∈ (bs.subst σ).fv,
      (y ∈ bs.fv ∧ y ∉ σ.map Prod.fst) ∨ y ∈ σ.map Prod.snd
  | σ, .nil => by simp [Binds.subst, Binds.fv]
  | σ, .cons x e bs => by
    intro y hy
    simp only [Binds.subst, Binds.fv, Finset.mem_union] at hy
    rcases hy with hy | hy
    · rcases fv_subst_e σ e y hy with ⟨hfv, hk⟩ | hv
      · exact Or.inl ⟨by simp [Binds.fv, hfv], hk⟩
      · exact Or.inr hv
    · rcases fv_subst_b σ bs y hy with ⟨hfv, hk⟩ | hv
      · exact Or.inl ⟨by simp [Binds.fv, hfv], hk⟩
      · exact Or.inr hv

end

/-- Every free name of a substitution instance is a free name of the expression that is not a
key of `σ`, or a value of `σ`. -/
theorem Expr.fv_subst {V : Type u} [DecidableEq V] (σ : List (V × V)) (e : Expr V) :
    (e.subst σ).fv ⊆ (e.fv \ (σ.map Prod.fst).toFinset) ∪ (σ.map Prod.snd).toFinset := by
  intro y hy
  rcases fv_subst_e σ e y hy with ⟨h₁, h₂⟩ | h
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h₁, by simpa using h₂⟩)
  · exact Finset.mem_union_right _ (by simpa using h)

/-- Every free name of a substitution instance of bindings is a free name of their right-hand
sides that is not a key of `σ`, or a value of `σ`. -/
theorem Binds.fv_subst {V : Type u} [DecidableEq V] (σ : List (V × V)) (bs : Binds V) :
    (bs.subst σ).fv ⊆ (bs.fv \ (σ.map Prod.fst).toFinset) ∪ (σ.map Prod.snd).toFinset := by
  intro y hy
  rcases fv_subst_b σ bs y hy with ⟨h₁, h₂⟩ | h
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h₁, by simpa using h₂⟩)
  · exact Finset.mem_union_right _ (by simpa using h)

/-- Looking up a renamed name in a renamed substitution list renames the result. -/
private theorem lookup_map_map {V : Type u} [DecidableEq V] {f : V → V}
    (hf : Function.Injective f) (σ : List (V × V)) (x : V) :
    (σ.map (Prod.map f f)).lookup (f x) = (σ.lookup x).map f := by
  induction σ with
  | nil => rfl
  | cons q σ ih =>
    obtain ⟨k, p⟩ := q
    simp only [List.map_cons, Prod.map_apply, List.lookup_cons]
    by_cases hxk : x = k
    · subst hxk
      simp
    · have hb : (x == k) = false := by simpa using hxk
      have hb' : (f x == f k) = false := by simpa using fun h => hxk (hf h)
      rw [hb, hb']
      exact ih

/-- The default of a renamed option at a renamed name is the renamed default. -/
private theorem getD_map_apply {V : Type u} (f : V → V) (o : Option V) (x : V) :
    (o.map f).getD (f x) = f (o.getD x) := by
  cases o <;> rfl

/-- Renaming commutes with removing the pairs whose key is a given name. -/
private theorem filter_ne_map {V : Type u} [DecidableEq V] {f : V → V}
    (hf : Function.Injective f) (σ : List (V × V)) (x : V) :
    (σ.filter fun q => q.1 ≠ x).map (Prod.map f f) =
      (σ.map (Prod.map f f)).filter fun q => q.1 ≠ f x := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro q _
  simp only [Function.comp_apply, Prod.map_fst, ne_eq, hf.eq_iff]

/-- Renaming commutes with removing the pairs whose key is in a list. -/
private theorem filter_nmem_map {V : Type u} [DecidableEq V] {f : V → V}
    (hf : Function.Injective f) (σ : List (V × V)) (l : List V) :
    (σ.filter fun q => q.1 ∉ l).map (Prod.map f f) =
      (σ.map (Prod.map f f)).filter fun q => q.1 ∉ l.map f := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro q _
  simp only [Function.comp_apply, Prod.map_fst, List.mem_map_of_injective hf]

/-- Renaming bindings renames their bound names. -/
private theorem vars_map {V : Type u} (f : V → V) :
    ∀ bs : Binds V, (bs.map f).vars = bs.vars.map f
  | .nil => rfl
  | .cons x e bs => by rw [Binds.map, Binds.vars, Binds.vars, vars_map f bs, List.map_cons]

mutual

/-- Renaming by an injective function commutes with substitution (both twins at once). -/
private theorem map_subst_e {V : Type u} [DecidableEq V] {f : V → V}
    (hf : Function.Injective f) :
    ∀ (σ : List (V × V)) (e : Expr V), (e.subst σ).map f = (e.map f).subst (σ.map (Prod.map f f))
  | σ, .var x => by
    simp only [Expr.subst, Expr.map, lookup_map_map hf, getD_map_apply]
  | σ, .lam x e => by
    simp only [Expr.subst, Expr.map, map_subst_e hf (σ.filter fun q => q.1 ≠ x) e,
      filter_ne_map hf]
  | σ, .app e x => by
    simp only [Expr.subst, Expr.map, map_subst_e hf σ e, lookup_map_map hf, getD_map_apply]
  | σ, .letrec bs e => by
    simp only [Expr.subst, Expr.map, map_subst_b hf (σ.filter fun q => q.1 ∉ bs.vars) bs,
      map_subst_e hf (σ.filter fun q => q.1 ∉ bs.vars) e, filter_nmem_map hf, vars_map]
  | σ, .num k => rfl
  | σ, .add e₁ e₂ => by
    simp only [Expr.subst, Expr.map, map_subst_e hf σ e₁, map_subst_e hf σ e₂]

/-- Renaming bindings by an injective function commutes with substitution. -/
private theorem map_subst_b {V : Type u} [DecidableEq V] {f : V → V}
    (hf : Function.Injective f) :
    ∀ (σ : List (V × V)) (bs : Binds V),
      (bs.subst σ).map f = (bs.map f).subst (σ.map (Prod.map f f))
  | σ, .nil => rfl
  | σ, .cons x e bs => by
    simp only [Binds.subst, Binds.map, map_subst_e hf σ e, map_subst_b hf σ bs]

end

/-- Renaming by an injective function commutes with substitution, which is renamed along. -/
theorem Expr.map_subst {V : Type u} [DecidableEq V] {f : V → V} (hf : Function.Injective f)
    (σ : List (V × V)) (e : Expr V) :
    (e.subst σ).map f = (e.map f).subst (σ.map (Prod.map f f)) := map_subst_e hf σ e

/-- Renaming bindings by an injective function commutes with substitution, which is renamed
along. -/
theorem Binds.map_subst {V : Type u} [DecidableEq V] {f : V → V} (hf : Function.Injective f)
    (σ : List (V × V)) (bs : Binds V) :
    (bs.subst σ).map f = (bs.map f).subst (σ.map (Prod.map f f)) := map_subst_b hf σ bs

mutual

/-- Names of a renamed expression (both twins at once). -/
private theorem names_map_e {V : Type u} [DecidableEq V] (f : V → V) :
    ∀ e : Expr V, (e.map f).names = e.names.image f
  | .var x => by simp [Expr.map, Expr.names]
  | .lam x e => by simp [Expr.map, Expr.names, names_map_e f e, Finset.image_insert]
  | .app e x => by simp [Expr.map, Expr.names, names_map_e f e, Finset.image_insert]
  | .letrec bs e => by
    simp [Expr.map, Expr.names, names_map_b f bs, names_map_e f e, Finset.image_union]
  | .num k => by simp [Expr.map, Expr.names]
  | .add e₁ e₂ => by
    simp [Expr.map, Expr.names, names_map_e f e₁, names_map_e f e₂, Finset.image_union]

/-- Names of renamed bindings. -/
private theorem names_map_b {V : Type u} [DecidableEq V] (f : V → V) :
    ∀ bs : Binds V, (bs.map f).names = bs.names.image f
  | .nil => by simp [Binds.map, Binds.names]
  | .cons x e bs => by
    simp [Binds.map, Binds.names, names_map_e f e, names_map_b f bs, Finset.image_insert,
      Finset.image_union]

end

/-- The names of a renamed expression are the images of its names. -/
theorem Expr.names_map {V : Type u} [DecidableEq V] (f : V → V) (e : Expr V) :
    (e.map f).names = e.names.image f := names_map_e f e

/-- The names of renamed bindings are the images of their names. -/
theorem Binds.names_map {V : Type u} [DecidableEq V] (f : V → V) (bs : Binds V) :
    (bs.map f).names = bs.names.image f := names_map_b f bs

mutual

/-- Renaming twice (both twins at once). -/
private theorem map_comp_e {V : Type u} (f g : V → V) :
    ∀ e : Expr V, (e.map f).map g = e.map (g ∘ f)
  | .var x => rfl
  | .lam x e => by simp only [Expr.map, map_comp_e f g e, Function.comp_apply]
  | .app e x => by simp only [Expr.map, map_comp_e f g e, Function.comp_apply]
  | .letrec bs e => by simp only [Expr.map, map_comp_b f g bs, map_comp_e f g e]
  | .num k => rfl
  | .add e₁ e₂ => by simp only [Expr.map, map_comp_e f g e₁, map_comp_e f g e₂]

/-- Renaming bindings twice. -/
private theorem map_comp_b {V : Type u} (f g : V → V) :
    ∀ bs : Binds V, (bs.map f).map g = bs.map (g ∘ f)
  | .nil => rfl
  | .cons x e bs => by
    simp only [Binds.map, map_comp_e f g e, map_comp_b f g bs, Function.comp_apply]

end

/-- Renaming twice is renaming by the composite. -/
theorem Expr.map_comp {V : Type u} (f g : V → V) (e : Expr V) :
    (e.map f).map g = e.map (g ∘ f) := map_comp_e f g e

/-- Renaming bindings twice is renaming them by the composite. -/
theorem Binds.map_comp {V : Type u} (f g : V → V) (bs : Binds V) :
    (bs.map f).map g = bs.map (g ∘ f) := map_comp_b f g bs

mutual

/-- Renaming by the identity (both twins at once). -/
private theorem map_id_e {V : Type u} : ∀ e : Expr V, e.map id = e
  | .var x => rfl
  | .lam x e => by simp only [Expr.map, map_id_e e, id]
  | .app e x => by simp only [Expr.map, map_id_e e, id]
  | .letrec bs e => by simp only [Expr.map, map_id_b bs, map_id_e e]
  | .num k => rfl
  | .add e₁ e₂ => by simp only [Expr.map, map_id_e e₁, map_id_e e₂]

/-- Renaming bindings by the identity. -/
private theorem map_id_b {V : Type u} : ∀ bs : Binds V, bs.map id = bs
  | .nil => rfl
  | .cons x e bs => by simp only [Binds.map, map_id_e e, map_id_b bs, id]

end

/-- Renaming by the identity changes nothing. -/
theorem Expr.map_id {V : Type u} (e : Expr V) : e.map id = e := map_id_e e

/-- Renaming bindings by the identity changes nothing. -/
theorem Binds.map_id {V : Type u} (bs : Binds V) : bs.map id = bs := map_id_b bs

mutual

/-- A function fixing every name of an expression renames it to itself (both twins at once). -/
private theorem map_eq_self_e {V : Type u} [DecidableEq V] {f : V → V} :
    ∀ e : Expr V, (∀ x ∈ e.names, f x = x) → e.map f = e
  | .var x, h => by simp [Expr.map, h x (by simp [Expr.names])]
  | .lam x e, h => by
    have hx := h x (by simp [Expr.names])
    have he := map_eq_self_e e fun y hy => h y (by simp [Expr.names, hy])
    simp only [Expr.map, hx, he]
  | .app e x, h => by
    have hx := h x (by simp [Expr.names])
    have he := map_eq_self_e e fun y hy => h y (by simp [Expr.names, hy])
    simp only [Expr.map, hx, he]
  | .letrec bs e, h => by
    have hb := map_eq_self_b bs fun y hy => h y (by simp [Expr.names, hy])
    have he := map_eq_self_e e fun y hy => h y (by simp [Expr.names, hy])
    simp only [Expr.map, hb, he]
  | .num k, _ => rfl
  | .add e₁ e₂, h => by
    have h₁ := map_eq_self_e e₁ fun y hy => h y (by simp [Expr.names, hy])
    have h₂ := map_eq_self_e e₂ fun y hy => h y (by simp [Expr.names, hy])
    simp only [Expr.map, h₁, h₂]

/-- A function fixing every name of bindings renames them to themselves. -/
private theorem map_eq_self_b {V : Type u} [DecidableEq V] {f : V → V} :
    ∀ bs : Binds V, (∀ x ∈ bs.names, f x = x) → bs.map f = bs
  | .nil, _ => rfl
  | .cons x e bs, h => by
    have hx := h x (by simp [Binds.names])
    have he := map_eq_self_e e fun y hy => h y (by simp [Binds.names, hy])
    have hb := map_eq_self_b bs fun y hy => h y (by simp [Binds.names, hy])
    simp only [Binds.map, hx, he, hb]

end

/-- A function that fixes every name of an expression renames it to itself. -/
theorem Expr.map_eq_self {V : Type u} [DecidableEq V] {f : V → V} {e : Expr V}
    (h : ∀ x ∈ e.names, f x = x) : e.map f = e := map_eq_self_e e h

/-- A function that fixes every name of bindings renames them to themselves. -/
theorem Binds.map_eq_self {V : Type u} [DecidableEq V] {f : V → V} {bs : Binds V}
    (h : ∀ x ∈ bs.names, f x = x) : bs.map f = bs := map_eq_self_b bs h

end Cslib.Languages.LambdaCalculus.CallByNeed
