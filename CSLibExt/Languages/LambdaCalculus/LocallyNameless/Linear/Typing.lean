/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasSubstitution
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Context

/-!
# Linear λ-calculus: typing, usage and linear substitution

The linear λ-calculus of multiplicative-additive linear logic (MALL), following Pfenning's
lecture notes on linear functional programming: types `1`, `A ⊗ B`, `A ⊸ B`, `A & B`, `A ⊕ B`,
`⊤`, `0` and base types, with the extrinsic judgment `Γ ⊢ t ∶ A` of section 2 of the notes.
Each hypothesis is used exactly once: the multiplicative rules partition the context, the
introduction of `&` and the branches of `⊕`-elimination share it, and the introduction of `⊤`
and the elimination of `0` may discard it. There are no exponentials.

## Representation

* Terms are locally nameless (`Term`): free variables are names in `Var`, bound variables are
  de Bruijn indices, and binders are opened (`Term.open'`, notation `t ^ s`) rather than
  renamed. `abs` binds one variable; the body of `casePair t u` binds two, `bvar 1` for the
  first component and `bvar 0` for the second (`Term.open₂`); each branch of `casePlus` binds
  one.
* Contexts are the lists of CSLib (`LocallyNameless.Context`), well formed when they have no
  duplicate names (`Γ✓`). The linear comma `Γ₁, Γ₂` of the notes is `Context.Split Γ Γ₁ Γ₂`:
  `Γ` is well formed and a permutation of `Γ₁ ++ Γ₂`, so `Γ₁` and `Γ₂` are disjoint.
* Binder rules quantify cofinitely over fresh names, as in CSLib's locally nameless simply
  typed λ-calculus.
* In the notes `⟨e₁, e₂⟩` is the tensor pair and `⟨⟩ : 1` the multiplicative unit, which
  needs the empty context; the additive pair `⟨|e₁, e₂|⟩ : A & B` is `Term.lpair` and
  `⟨| |⟩ : ⊤` is `Term.lunit`.

## Main statements

* `Typing.perm`: exchange, the structural rule that holds. `Typing.lc`: typed terms are
  locally closed.
* Usage, per rule kind: `Typing.var_iff`, `Typing.app_iff`, `Typing.pair_iff`,
  `Typing.casePair_iff`, `Typing.caseUnit_iff` (partition), `Typing.lpair_iff`,
  `Typing.casePlus_iff` (share), `Typing.lunit_iff`, `Typing.caseZero_iff` (discard), the
  other inversion lemmas, and their consequences on free variables: `Typing.fv_subset_dom`,
  `Typing.dom_subset_fv` (when no subterm discards), `Typing.pair_fv_disjoint` and its
  siblings, `Typing.lpair_fv_eq`, `Typing.casePlus_fv_eq`.
* Exactly once, on the purely multiplicative fragment: `Typing.occ_eq_one`.
* Linear substitution (Property 1 of the notes): `Typing.subst`, with the opening forms
  `Typing.open_subst` and `Typing.open₂_subst` used by β-steps.

The usage and exactly-once statements make precise the notes' informal "each hypothesis is
used exactly once"; the notes give the rules and Property 1 but do not state these lemmas.

## Fresh names

The statements that need fresh names assume `[HasFresh Var]`: every finite set of names misses
some name. On terms these are `Term.open_lc`, `Term.subst_open`, `Term.subst_open_var`,
`Term.subst_lc`, `Term.beta_lc`, `Term.casePair_lc_open₂`, `Term.casePlus_lc_open_left` and
`Term.casePlus_lc_open_right`. On typing they are `Typing.wf`, `Typing.fv_subset_dom`,
`Typing.dom_subset_fv`, `Typing.occ_eq_one`, `Typing.occ_eq_zero`, `Typing.app_fv_disjoint`,
`Typing.pair_fv_disjoint`, `Typing.casePair_fv_disjoint`, `Typing.caseUnit_fv_disjoint`,
`Typing.casePlus_fv_disjoint`, `Typing.lpair_fv_eq`, `Typing.casePlus_fv_eq`, `Typing.subst`,
`Typing.open_subst` and `Typing.open₂_subst`. Over a finite type of names a cofinite premise can
quantify over no name at all, so every abstraction is locally closed and `abs` types every
abstraction in every context; these statements are then false, and a well-formedness premise on
`abs` would repair only `Typing.wf`.

## References

* F. Pfenning, *Lecture Notes on Linear Functional Programming*, 15-814 Types and Programming
  Languages, Lecture 19, Carnegie Mellon University, Fall 2025: section 2 (typing rules) and
  section 3 (Property 1, linear substitution).
  <http://www.cs.cmu.edu/afs/cs.cmu.edu/user/fp/www/courses/15814-f25/lectures/19-linfun.pdf>
* A. Charguéraud, *The Locally Nameless Representation*, Journal of Automated Reasoning 49
  (2012).
-/

@[expose] public section

namespace Cslib

universe u v

namespace LambdaCalculus.LocallyNameless

/-! ### Splitting contexts -/

namespace Context

variable {α : Type u} {β : Type v}

/-- `Γ.Split Γ₁ Γ₂`: the well-formed context `Γ` is a permutation of `Γ₁ ++ Γ₂`. This is the
linear comma `Γ₁, Γ₂`; since `Γ` has no duplicate names, `Γ₁` and `Γ₂` are disjoint. -/
def Split (Γ Γ₁ Γ₂ : Context α β) : Prop := Γ✓ ∧ Γ.Perm (Γ₁ ++ Γ₂)

variable {Γ Γ₁ Γ₂ Δ Δ₁ : Context α β}

/-- The whole context of a split is well formed. -/
theorem Split.wf (h : Γ.Split Γ₁ Γ₂) : Γ✓ := h.1

/-- The whole context of a split is a permutation of the concatenation of its parts. -/
theorem Split.perm (h : Γ.Split Γ₁ Γ₂) : Γ.Perm (Γ₁ ++ Γ₂) := h.2

/-- The left part of a split is well formed. -/
theorem Split.wf_left (h : Γ.Split Γ₁ Γ₂) : Γ₁✓ :=
  List.NodupKeys.sublist (List.sublist_append_left _ _) ((List.perm_nodupKeys h.2).1 h.1)

/-- The right part of a split is well formed. -/
theorem Split.wf_right (h : Γ.Split Γ₁ Γ₂) : Γ₂✓ :=
  List.NodupKeys.sublist (List.sublist_append_right _ _) ((List.perm_nodupKeys h.2).1 h.1)

/-- The concatenation of the parts of a split is well formed. -/
theorem Split.wf_append (h : Γ.Split Γ₁ Γ₂) : (Γ₁ ++ Γ₂)✓ := (List.perm_nodupKeys h.2).1 h.1

/-- A split is symmetric in its parts. -/
theorem Split.symm (h : Γ.Split Γ₁ Γ₂) : Γ.Split Γ₂ Γ₁ := ⟨h.1, h.2.trans List.perm_append_comm⟩

/-- A split is invariant under permuting the whole context. -/
theorem Split.perm_whole (h : Γ.Split Γ₁ Γ₂) (hp : Γ.Perm Δ) : Δ.Split Γ₁ Γ₂ :=
  ⟨(List.perm_nodupKeys hp).1 h.1, hp.symm.trans h.2⟩

/-- A split is invariant under permuting its left part. -/
theorem Split.perm_left (h : Γ.Split Γ₁ Γ₂) (hp : Γ₁.Perm Δ₁) : Γ.Split Δ₁ Γ₂ :=
  ⟨h.1, h.2.trans (hp.append_right Γ₂)⟩

/-- A well-formed concatenation splits into its two pieces. -/
theorem split_append_iff : (Γ₁ ++ Γ₂).Split Γ₁ Γ₂ ↔ (Γ₁ ++ Γ₂)✓ :=
  ⟨fun h => h.1, fun h => ⟨h, List.Perm.refl _⟩⟩

/-- Splitting off the empty context. -/
theorem split_nil_left_iff : Γ.Split [] Δ ↔ Γ✓ ∧ Γ.Perm Δ := Iff.rfl

variable [DecidableEq α]

/-- The parts of a split have disjoint domains. -/
theorem Split.disjoint (h : Γ.Split Γ₁ Γ₂) : Disjoint Γ₁.dom Γ₂.dom := by
  have hk : (Γ₁.keys ++ Γ₂.keys).Nodup := by
    have := h.wf_append
    simpa [HasWellFormed.wf, List.NodupKeys, List.keys_append] using this
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [dom, List.mem_toFinset] at ha hb
  exact List.disjoint_of_nodup_append hk ha hb

/-- The domain of a split context is the union of the domains of its parts. -/
theorem Split.dom_eq (h : Γ.Split Γ₁ Γ₂) : Γ.dom = Γ₁.dom ∪ Γ₂.dom := by
  have hk : Γ.keys.Perm (Γ₁.keys ++ Γ₂.keys) := by
    simpa [List.keys, List.map_append] using h.2.map Sigma.fst
  simp only [dom]
  rw [List.toFinset_eq_of_perm _ _ hk, List.toFinset_append]

end Context

namespace Linear

/-! ### Types -/

/-- Types of the linear λ-calculus of multiplicative-additive linear logic. Constructor names
follow `Cslib.Logic.CLL.Proposition`. -/
inductive Ty (Base : Type v)
  /-- A base type. -/
  | base : Base → Ty Base
  /-- The multiplicative unit `1`. -/
  | one : Ty Base
  /-- Multiplicative conjunction `A ⊗ B`. -/
  | tensor : Ty Base → Ty Base → Ty Base
  /-- Linear implication `A ⊸ B`. -/
  | lolli : Ty Base → Ty Base → Ty Base
  /-- Additive conjunction `A & B`. -/
  | with : Ty Base → Ty Base → Ty Base
  /-- Additive disjunction `A ⊕ B`. -/
  | oplus : Ty Base → Ty Base → Ty Base
  /-- The additive unit `⊤`. -/
  | top : Ty Base
  /-- The additive zero `0`. -/
  | zero : Ty Base
  deriving DecidableEq

@[inherit_doc] scoped infixr:35 " ⊗ " => Ty.tensor
@[inherit_doc] scoped infixr:35 " ⊕ " => Ty.oplus
@[inherit_doc] scoped infixr:30 " & " => Ty.with
@[inherit_doc] scoped infixr:25 " ⊸ " => Ty.lolli

/-! ### Terms -/

/-- Locally nameless terms over free names `Var`. In the syntax of Pfenning's lecture notes on
linear functional programming (15-814, Lecture 19): `abs` is `λx. e`, `pair` is the tensor pair
`⟨e₁, e₂⟩`, `casePair t u` is `case t (⟨x, y⟩ ⇒ u)`, `unit` is `⟨⟩`, `caseUnit t u` is
`case t (⟨⟩ ⇒ u)`, `lpair` is `⟨|e₁, e₂|⟩`, `proj₁` and `proj₂` are the projections, `inl` and `inr`
are `l · e` and `r · e`, `casePlus t u v` is `case t (l · x ⇒ u | r · y ⇒ v)`, `lunit` is `⟨| |⟩`
and `caseZero t` is `case t ( )`. -/
inductive Term (Var : Type u)
  /-- A bound variable, as a de Bruijn index. -/
  | bvar : ℕ → Term Var
  /-- A free variable. -/
  | fvar : Var → Term Var
  /-- Abstraction, binding one variable. -/
  | abs : Term Var → Term Var
  /-- Application. -/
  | app : Term Var → Term Var → Term Var
  /-- The tensor pair. -/
  | pair : Term Var → Term Var → Term Var
  /-- Tensor elimination; the second argument binds two variables, `bvar 1` for the first
  component and `bvar 0` for the second. -/
  | casePair : Term Var → Term Var → Term Var
  /-- The multiplicative unit. -/
  | unit : Term Var
  /-- Elimination of the multiplicative unit. -/
  | caseUnit : Term Var → Term Var → Term Var
  /-- The additive (with) pair. -/
  | lpair : Term Var → Term Var → Term Var
  /-- First projection of an additive pair. -/
  | proj₁ : Term Var → Term Var
  /-- Second projection of an additive pair. -/
  | proj₂ : Term Var → Term Var
  /-- Left injection into a sum. -/
  | inl : Term Var → Term Var
  /-- Right injection into a sum. -/
  | inr : Term Var → Term Var
  /-- Sum elimination; each branch binds one variable. -/
  | casePlus : Term Var → Term Var → Term Var → Term Var
  /-- The additive unit. -/
  | lunit : Term Var
  /-- Elimination of the additive zero. -/
  | caseZero : Term Var → Term Var
  deriving DecidableEq

namespace Term

variable {Var : Type u}

/-- Opening: replace the bound variable of index `k` by `s`. The index grows by one under `abs`
and under each branch of `casePlus`, and by two under the body of `casePair`. -/
def openRec (k : ℕ) (s : Term Var) : Term Var → Term Var
  | bvar i => if k = i then s else bvar i
  | fvar x => fvar x
  | abs t => abs (openRec (k + 1) s t)
  | app t₁ t₂ => app (openRec k s t₁) (openRec k s t₂)
  | pair t₁ t₂ => pair (openRec k s t₁) (openRec k s t₂)
  | casePair t u => casePair (openRec k s t) (openRec (k + 2) s u)
  | unit => unit
  | caseUnit t u => caseUnit (openRec k s t) (openRec k s u)
  | lpair t₁ t₂ => lpair (openRec k s t₁) (openRec k s t₂)
  | proj₁ t => proj₁ (openRec k s t)
  | proj₂ t => proj₂ (openRec k s t)
  | inl t => inl (openRec k s t)
  | inr t => inr (openRec k s t)
  | casePlus t u v => casePlus (openRec k s t) (openRec (k + 1) s u) (openRec (k + 1) s v)
  | lunit => lunit
  | caseZero t => caseZero (openRec k s t)

@[inherit_doc]
scoped notation:68 e "⟦" k " ↝ " s "⟧" => Term.openRec k s e

/-- Opening of the outermost bound variable. -/
def open' (t s : Term Var) : Term Var := openRec 0 s t

@[inherit_doc]
scoped infixr:80 " ^ " => Term.open'

/-- Opening of the two variables bound by the body of `casePair`: `bvar 1` becomes `s₁`, the
first component, and `bvar 0` becomes `s₂`, the second. -/
def open₂ (t s₁ s₂ : Term Var) : Term Var := openRec 0 s₂ (openRec 1 s₁ t)

/-- Local closure: no bound variable is dangling. Binders quantify cofinitely over fresh
names. -/
inductive LC : Term Var → Prop
  | fvar (x : Var) : LC (fvar x)
  | abs (L : Finset Var) {t : Term Var} : (∀ x ∉ L, LC (t ^ fvar x)) → LC (abs t)
  | app {t₁ t₂ : Term Var} : LC t₁ → LC t₂ → LC (app t₁ t₂)
  | pair {t₁ t₂ : Term Var} : LC t₁ → LC t₂ → LC (pair t₁ t₂)
  | casePair (L : Finset Var) {t u : Term Var} : LC t →
      (∀ x ∉ L, ∀ y ∉ L, x ≠ y → LC (u.open₂ (fvar x) (fvar y))) → LC (casePair t u)
  | unit : LC unit
  | caseUnit {t u : Term Var} : LC t → LC u → LC (caseUnit t u)
  | lpair {t₁ t₂ : Term Var} : LC t₁ → LC t₂ → LC (lpair t₁ t₂)
  | proj₁ {t : Term Var} : LC t → LC (proj₁ t)
  | proj₂ {t : Term Var} : LC t → LC (proj₂ t)
  | inl {t : Term Var} : LC t → LC (inl t)
  | inr {t : Term Var} : LC t → LC (inr t)
  | casePlus (L : Finset Var) {t u v : Term Var} : LC t → (∀ x ∉ L, LC (u ^ fvar x)) →
      (∀ y ∉ L, LC (v ^ fvar y)) → LC (casePlus t u v)
  | lunit : LC lunit
  | caseZero {t : Term Var} : LC t → LC (caseZero t)

/-- The purely multiplicative fragment: terms built from variables, `abs`, `app`, `pair`,
`casePair`, `unit` and `caseUnit` only. Types are unrestricted. -/
def Multiplicative : Term Var → Prop
  | bvar _ => True
  | fvar _ => True
  | abs t => t.Multiplicative
  | app t₁ t₂ => t₁.Multiplicative ∧ t₂.Multiplicative
  | pair t₁ t₂ => t₁.Multiplicative ∧ t₂.Multiplicative
  | casePair t u => t.Multiplicative ∧ u.Multiplicative
  | unit => True
  | caseUnit t u => t.Multiplicative ∧ u.Multiplicative
  | lpair _ _ => False
  | proj₁ _ => False
  | proj₂ _ => False
  | inl _ => False
  | inr _ => False
  | casePlus _ _ _ => False
  | lunit => False
  | caseZero _ => False

/-- Terms with no subterm `lunit` or `caseZero`, the two forms whose rules discard
hypotheses. -/
def NoDiscard : Term Var → Prop
  | bvar _ => True
  | fvar _ => True
  | abs t => t.NoDiscard
  | app t₁ t₂ => t₁.NoDiscard ∧ t₂.NoDiscard
  | pair t₁ t₂ => t₁.NoDiscard ∧ t₂.NoDiscard
  | casePair t u => t.NoDiscard ∧ u.NoDiscard
  | unit => True
  | caseUnit t u => t.NoDiscard ∧ u.NoDiscard
  | lpair t₁ t₂ => t₁.NoDiscard ∧ t₂.NoDiscard
  | proj₁ t => t.NoDiscard
  | proj₂ t => t.NoDiscard
  | inl t => t.NoDiscard
  | inr t => t.NoDiscard
  | casePlus t u v => t.NoDiscard ∧ u.NoDiscard ∧ v.NoDiscard
  | lunit => False
  | caseZero _ => False

variable [DecidableEq Var]

/-- The free variables of a term. -/
def fv : Term Var → Finset Var
  | bvar _ => ∅
  | fvar x => {x}
  | abs t => t.fv
  | app t₁ t₂ => t₁.fv ∪ t₂.fv
  | pair t₁ t₂ => t₁.fv ∪ t₂.fv
  | casePair t u => t.fv ∪ u.fv
  | unit => ∅
  | caseUnit t u => t.fv ∪ u.fv
  | lpair t₁ t₂ => t₁.fv ∪ t₂.fv
  | proj₁ t => t.fv
  | proj₂ t => t.fv
  | inl t => t.fv
  | inr t => t.fv
  | casePlus t u v => t.fv ∪ u.fv ∪ v.fv
  | lunit => ∅
  | caseZero t => t.fv

/-- The number of free occurrences of the name `x` in a term. -/
def occ (x : Var) : Term Var → ℕ
  | bvar _ => 0
  | fvar y => if x = y then 1 else 0
  | abs t => t.occ x
  | app t₁ t₂ => t₁.occ x + t₂.occ x
  | pair t₁ t₂ => t₁.occ x + t₂.occ x
  | casePair t u => t.occ x + u.occ x
  | unit => 0
  | caseUnit t u => t.occ x + u.occ x
  | lpair t₁ t₂ => t₁.occ x + t₂.occ x
  | proj₁ t => t.occ x
  | proj₂ t => t.occ x
  | inl t => t.occ x
  | inr t => t.occ x
  | casePlus t u v => t.occ x + u.occ x + v.occ x
  | lunit => 0
  | caseZero t => t.occ x

/-- Substitution of `s` for the free variable `x`. -/
def subst (t : Term Var) (x : Var) (s : Term Var) : Term Var :=
  match t with
  | bvar i => bvar i
  | fvar y => if x = y then s else fvar y
  | abs t => abs (t.subst x s)
  | app t₁ t₂ => app (t₁.subst x s) (t₂.subst x s)
  | pair t₁ t₂ => pair (t₁.subst x s) (t₂.subst x s)
  | casePair t u => casePair (t.subst x s) (u.subst x s)
  | unit => unit
  | caseUnit t u => caseUnit (t.subst x s) (u.subst x s)
  | lpair t₁ t₂ => lpair (t₁.subst x s) (t₂.subst x s)
  | proj₁ t => proj₁ (t.subst x s)
  | proj₂ t => proj₂ (t.subst x s)
  | inl t => inl (t.subst x s)
  | inr t => inr (t.subst x s)
  | casePlus t u v => casePlus (t.subst x s) (u.subst x s) (v.subst x s)
  | lunit => lunit
  | caseZero t => caseZero (t.subst x s)

/-- `Term.subst` gives the notation `t[x := s]`. -/
instance instHasSubstitutionTerm : HasSubstitution (Term Var) Var (Term Var) where
  subst := Term.subst

/-! #### Laws of the locally nameless operations -/

variable {t u v s s₁ s₂ : Term Var} {x y : Var}

omit [DecidableEq Var] in
/-- Opening at an index other than `j` is invisible if it is invisible after opening at `j`. -/
private theorem openRec_core {t u v : Term Var} {i j : ℕ} (hij : i ≠ j)
    (h : (t⟦j ↝ u⟧)⟦i ↝ v⟧ = t⟦j ↝ u⟧) : t⟦i ↝ v⟧ = t := by
  induction t generalizing i j with
  | bvar n =>
    by_cases hjn : j = n
    · subst hjn; simp [openRec, hij]
    · simpa [openRec, hjn] using h
  | fvar _ => rfl
  | unit => rfl
  | lunit => rfl
  | abs t ih =>
    simp only [openRec, abs.injEq] at h ⊢
    exact ih (by omega) h
  | app t₁ t₂ ih₁ ih₂ =>
    simp only [openRec, app.injEq] at h ⊢
    exact ⟨ih₁ hij h.1, ih₂ hij h.2⟩
  | pair t₁ t₂ ih₁ ih₂ =>
    simp only [openRec, pair.injEq] at h ⊢
    exact ⟨ih₁ hij h.1, ih₂ hij h.2⟩
  | casePair t₁ t₂ ih₁ ih₂ =>
    simp only [openRec, casePair.injEq] at h ⊢
    exact ⟨ih₁ hij h.1, ih₂ (by omega) h.2⟩
  | caseUnit t₁ t₂ ih₁ ih₂ =>
    simp only [openRec, caseUnit.injEq] at h ⊢
    exact ⟨ih₁ hij h.1, ih₂ hij h.2⟩
  | lpair t₁ t₂ ih₁ ih₂ =>
    simp only [openRec, lpair.injEq] at h ⊢
    exact ⟨ih₁ hij h.1, ih₂ hij h.2⟩
  | proj₁ t ih =>
    simp only [openRec, proj₁.injEq] at h ⊢
    exact ih hij h
  | proj₂ t ih =>
    simp only [openRec, proj₂.injEq] at h ⊢
    exact ih hij h
  | inl t ih =>
    simp only [openRec, inl.injEq] at h ⊢
    exact ih hij h
  | inr t ih =>
    simp only [openRec, inr.injEq] at h ⊢
    exact ih hij h
  | casePlus t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    simp only [openRec, casePlus.injEq] at h ⊢
    exact ⟨ih₁ hij h.1, ih₂ (by omega) h.2.1, ih₃ (by omega) h.2.2⟩
  | caseZero t ih =>
    simp only [openRec, caseZero.injEq] at h ⊢
    exact ih hij h

/-- The substitution notation unfolds to `Term.subst`. -/
private theorem subst_eq : t[x := s] = t.subst x s := rfl

/-- Opening at any index by a term is opening by a fresh name followed by substitution. -/
private theorem subst_intro_openRec (k : ℕ) (h : x ∉ t.fv) :
    t⟦k ↝ s⟧ = (t⟦k ↝ fvar x⟧)[x := s] := by
  rw [subst_eq]
  induction t generalizing k with
  | bvar i => by_cases hk : k = i <;> simp [openRec, subst, hk]
  | fvar y =>
    have : x ≠ y := by simpa [fv] using h
    simp [openRec, subst, this]
  | _ => simp_all [openRec, subst, fv]

/-- Opening adds at most the free variables of the inserted term. -/
private theorem fv_openRec_subset (k : ℕ) : (t⟦k ↝ s⟧).fv ⊆ t.fv ∪ s.fv := by
  induction t generalizing k with
  | bvar i =>
    by_cases hk : k = i <;> simp [openRec, fv, hk]
  | _ =>
    simp only [openRec, fv]
    intro z hz
    simp only [Finset.mem_union] at *
    grind

/-- Opening keeps every free variable. -/
private theorem fv_subset_fv_openRec (k : ℕ) : t.fv ⊆ (t⟦k ↝ s⟧).fv := by
  induction t generalizing k with
  | _ =>
    intro z hz
    simp only [openRec, fv, Finset.mem_union] at *
    first | done | grind

/-- Opening by another name does not change the occurrences of `y`. -/
private theorem occ_openRec_fvar (k : ℕ) (hyx : y ≠ x) : (t⟦k ↝ fvar x⟧).occ y = t.occ y := by
  induction t generalizing k with
  | bvar i => by_cases hk : k = i <;> simp [openRec, occ, hk, hyx]
  | _ => simp_all [openRec, occ]

omit [DecidableEq Var] in
/-- Opening by a name stays in the multiplicative fragment. -/
private theorem multiplicative_openRec_fvar (k : ℕ) (h : t.Multiplicative) :
    (t⟦k ↝ fvar x⟧).Multiplicative := by
  induction t generalizing k with
  | bvar i => by_cases hk : k = i <;> simp [openRec, Multiplicative, hk]
  | _ => simp_all [openRec, Multiplicative]

omit [DecidableEq Var] in
/-- Opening by a name introduces no discarding form. -/
private theorem noDiscard_openRec_fvar (k : ℕ) (h : t.NoDiscard) : (t⟦k ↝ fvar x⟧).NoDiscard := by
  induction t generalizing k with
  | bvar i => by_cases hk : k = i <;> simp [openRec, NoDiscard, hk]
  | _ => simp_all [openRec, NoDiscard]

/-- A name occurs in a term exactly when it is free in it. -/
theorem occ_eq_zero_iff : t.occ x = 0 ↔ x ∉ t.fv := by
  induction t <;> simp_all [occ, fv, and_assoc]

/-- Substituting for a name that is not free leaves the term unchanged. -/
theorem subst_fresh (h : x ∉ t.fv) : t[x := s] = t := by
  rw [subst_eq]
  induction t <;> simp_all [subst, fv]

/-- Opening by a term is opening by a fresh name followed by substitution. -/
theorem subst_intro (h : x ∉ t.fv) : t ^ s = (t ^ fvar x)[x := s] := subst_intro_openRec 0 h

variable [HasFresh Var]

omit [DecidableEq Var] in
/-- When every finite set of names misses some name (`[HasFresh Var]`), opening a locally closed
term leaves it unchanged. -/
theorem open_lc (k : ℕ) (s : Term Var) (h : t.LC) : t⟦k ↝ s⟧ = t := by
  classical
  induction h generalizing k with
  | fvar => rfl
  | unit => rfl
  | lunit => rfl
  | abs L _ ih =>
    obtain ⟨x, hx⟩ := fresh_exists L
    simp only [openRec, abs.injEq]
    exact openRec_core (by omega) (ih x hx (k + 1))
  | casePair L _ _ iht ihu =>
    obtain ⟨x, hx⟩ := fresh_exists L
    obtain ⟨y, hy⟩ := fresh_exists (insert x L)
    have hyL : y ∉ L := fun h => hy (Finset.mem_insert_of_mem h)
    have hxy : x ≠ y := fun h => hy (h ▸ Finset.mem_insert_self x L)
    simp only [openRec, casePair.injEq]
    refine ⟨iht k, ?_⟩
    have h2 := ihu x hx y hyL hxy (k + 2)
    exact openRec_core (by omega) (openRec_core (u := fvar y) (by omega) h2)
  | casePlus L _ _ _ iht ihu ihv =>
    obtain ⟨x, hx⟩ := fresh_exists L
    simp only [openRec, casePlus.injEq]
    exact ⟨iht k, openRec_core (by omega) (ihu x hx (k + 1)),
      openRec_core (by omega) (ihv x hx (k + 1))⟩
  | _ => simp_all [openRec]

/-- Substitution of a locally closed term commutes with opening at any index. -/
private theorem subst_openRec (hs : s.LC) (k : ℕ) :
    (t⟦k ↝ u⟧)[x := s] = (t[x := s])⟦k ↝ u[x := s]⟧ := by
  simp only [subst_eq]
  induction t generalizing k with
  | bvar i => by_cases hk : k = i <;> simp [openRec, subst, hk]
  | fvar y =>
    by_cases hxy : x = y
    · subst hxy; simp [openRec, subst, open_lc _ _ hs]
    · simp [openRec, subst, hxy]
  | _ => simp_all [openRec, subst]

/-- Free variables of a body bounded through cofinitely many fresh openings. -/
private theorem fv_subset_of_open {L D : Finset Var}
    (h : ∀ x ∉ L, (t ^ fvar x).fv ⊆ insert x D) : t.fv ⊆ D := by
  obtain ⟨x, hx⟩ := fresh_exists (L ∪ t.fv)
  simp only [Finset.mem_union, not_or] at hx
  intro z hz
  have hzx : z ≠ x := fun h => hx.2 (h ▸ hz)
  have := h x hx.1 (fv_subset_fv_openRec 0 hz)
  simpa [hzx] using this

/-- Free variables of a two-binder body bounded through fresh openings. -/
private theorem fv_subset_of_open₂ {L D : Finset Var}
    (h : ∀ x ∉ L, ∀ y ∉ L, x ≠ y → (t.open₂ (fvar x) (fvar y)).fv ⊆ insert y (insert x D)) :
    t.fv ⊆ D := by
  obtain ⟨x, hx⟩ := fresh_exists (L ∪ t.fv)
  obtain ⟨y, hy⟩ := fresh_exists (insert x (L ∪ t.fv))
  simp only [Finset.mem_insert, Finset.mem_union, not_or] at hx hy
  intro z hz
  have hzx : z ≠ x := fun h => hx.2 (h ▸ hz)
  have hzy : z ≠ y := fun h => hy.2.2 (h ▸ hz)
  have := h x hx.1 y hy.2.1 (Ne.symm hy.1)
    (fv_subset_fv_openRec 0 (fv_subset_fv_openRec 1 hz))
  simpa [hzx, hzy] using this

/-- A set covered by cofinitely many fresh openings of a body is covered by the body. -/
private theorem subset_fv_of_open {L D : Finset Var}
    (h : ∀ x ∉ L, insert x D ⊆ (t ^ fvar x).fv) : D ⊆ t.fv := by
  obtain ⟨x, hx⟩ := fresh_exists (L ∪ D)
  simp only [Finset.mem_union, not_or] at hx
  intro z hz
  have hzx : z ≠ x := fun h => hx.2 (h ▸ hz)
  have := fv_openRec_subset 0 (h x hx.1 (Finset.mem_insert_of_mem hz))
  simpa [fv, hzx] using this

/-- A set covered by fresh double openings of a two-binder body is covered by the body. -/
private theorem subset_fv_of_open₂ {L D : Finset Var}
    (h : ∀ x ∉ L, ∀ y ∉ L, x ≠ y → insert y (insert x D) ⊆ (t.open₂ (fvar x) (fvar y)).fv) :
    D ⊆ t.fv := by
  obtain ⟨x, hx⟩ := fresh_exists (L ∪ D)
  obtain ⟨y, hy⟩ := fresh_exists (insert x (L ∪ D))
  simp only [Finset.mem_insert, Finset.mem_union, not_or] at hx hy
  intro z hz
  have hzx : z ≠ x := fun h => hx.2 (h ▸ hz)
  have hzy : z ≠ y := fun h => hy.2.2 (h ▸ hz)
  have h1 := fv_openRec_subset 0
    (h x hx.1 y hy.2.1 (Ne.symm hy.1) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)))
  have h2 : z ∈ (t⟦1 ↝ fvar x⟧).fv := by simpa [fv, hzy] using h1
  simpa [fv, hzx] using fv_openRec_subset 1 h2

/-- When every finite set of names misses some name (`[HasFresh Var]`), substitution of a locally
closed term commutes with opening. -/
theorem subst_open (hs : s.LC) : (t ^ u)[x := s] = t[x := s] ^ u[x := s] := subst_openRec hs 0

/-- When every finite set of names misses some name (`[HasFresh Var]`), substitution of a locally
closed term commutes with opening by another name. -/
theorem subst_open_var (hxy : y ≠ x) (hs : s.LC) : (t ^ fvar y)[x := s] = t[x := s] ^ fvar y :=
  by
    rw [subst_open hs]
    simp [subst_eq, subst, Ne.symm hxy]

/-- Substitution commutes with the double opening by two other names. -/
private theorem subst_open₂_var {z w : Var} (hz : z ≠ x) (hw : w ≠ x) (hs : s.LC) :
    (t.open₂ (fvar z) (fvar w))[x := s] = (t[x := s]).open₂ (fvar z) (fvar w) := by
  simp only [open₂]
  rw [subst_openRec hs, subst_openRec hs]
  simp [subst_eq, subst, Ne.symm hz, Ne.symm hw]

/-- When every finite set of names misses some name (`[HasFresh Var]`), substitution of a locally
closed term preserves local closure. -/
theorem subst_lc (ht : t.LC) (hs : s.LC) : (t[x := s]).LC := by
  induction ht with
  | fvar y =>
    by_cases hxy : x = y
    · simpa [subst_eq, subst, hxy] using hs
    · simpa [subst_eq, subst, hxy] using LC.fvar y
  | abs L _ ih =>
    refine LC.abs (insert x L) fun z hz => ?_
    have hzL : z ∉ L := fun h => hz (Finset.mem_insert_of_mem h)
    have hzx : z ≠ x := fun h => hz (h ▸ Finset.mem_insert_self x L)
    have := ih z hzL
    rwa [subst_open_var hzx hs] at this
  | casePair L _ _ iht ihu =>
    refine LC.casePair (insert x L) iht fun z hz w hw hzw => ?_
    have hzL : z ∉ L := fun h => hz (Finset.mem_insert_of_mem h)
    have hzx : z ≠ x := fun h => hz (h ▸ Finset.mem_insert_self x L)
    have hwL : w ∉ L := fun h => hw (Finset.mem_insert_of_mem h)
    have hwx : w ≠ x := fun h => hw (h ▸ Finset.mem_insert_self x L)
    have := ihu z hzL w hwL hzw
    rwa [subst_open₂_var hzx hwx hs] at this
  | casePlus L _ _ _ iht ihu ihv =>
    refine LC.casePlus (insert x L) iht (fun z hz => ?_) (fun z hz => ?_)
    all_goals
      have hzL : z ∉ L := fun h => hz (Finset.mem_insert_of_mem h)
      have hzx : z ≠ x := fun h => hz (h ▸ Finset.mem_insert_self x L)
    · have := ihu z hzL
      rwa [subst_open_var hzx hs] at this
    · have := ihv z hzL
      rwa [subst_open_var hzx hs] at this
  | unit => exact LC.unit
  | lunit => exact LC.lunit
  | app _ _ ih₁ ih₂ => exact LC.app ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact LC.pair ih₁ ih₂
  | caseUnit _ _ ih₁ ih₂ => exact LC.caseUnit ih₁ ih₂
  | lpair _ _ ih₁ ih₂ => exact LC.lpair ih₁ ih₂
  | proj₁ _ ih => exact LC.proj₁ ih
  | proj₂ _ ih => exact LC.proj₂ ih
  | inl _ ih => exact LC.inl ih
  | inr _ ih => exact LC.inr ih
  | caseZero _ ih => exact LC.caseZero ih

omit [DecidableEq Var] in
/-- When every finite set of names misses some name (`[HasFresh Var]`), opening the body of a
locally closed abstraction by a locally closed term gives a locally closed term. -/
theorem beta_lc (h : (abs t).LC) (hs : s.LC) : (t ^ s).LC := by
  classical
  cases h with
  | abs L h =>
    obtain ⟨x, hx⟩ := fresh_exists (L ∪ t.fv)
    rw [subst_intro (x := x) (fun hm => hx (Finset.mem_union_right _ hm))]
    exact subst_lc (h x fun hm => hx (Finset.mem_union_left _ hm)) hs

/-- The double opening through fresh names, substituting the first component first. -/
private theorem open₂_eq_subst (hx : x ∉ u.fv) (hy : y ∉ u.fv) (hxy : y ≠ x) (hy₁ : y ∉ s₁.fv)
    (hs₁ : s₁.LC) : u.open₂ s₁ s₂ = ((u.open₂ (fvar x) (fvar y))[x := s₁])[y := s₂] := by
  simp only [open₂]
  rw [subst_openRec hs₁, ← subst_intro_openRec 1 hx]
  have : (fvar y : Term Var)[x := s₁] = fvar y := by simp [subst_eq, subst, Ne.symm hxy]
  rw [this, ← subst_intro_openRec 0]
  intro hmem
  rcases Finset.mem_union.1 (fv_openRec_subset 1 hmem) with h | h
  exacts [hy h, hy₁ h]

/-- The double opening through fresh names, substituting the second component first. -/
private theorem open₂_eq_subst_rev (hx : x ∉ u.fv) (hy : y ∉ u.fv) (hxy : y ≠ x)
    (hx₂ : x ∉ s₂.fv) (hs₁ : s₁.LC) :
    u.open₂ s₁ s₂ = ((u.open₂ (fvar x) (fvar y))[y := s₂])[x := s₁] := by
  simp only [open₂]
  rw [← subst_intro_openRec 0, subst_openRec hs₁, ← subst_intro_openRec 1 hx, subst_fresh hx₂]
  intro hmem
  rcases Finset.mem_union.1 (fv_openRec_subset 1 hmem) with h | h
  · exact hy h
  · exact hxy (by simpa [fv] using h)

omit [DecidableEq Var] in
/-- When every finite set of names misses some name (`[HasFresh Var]`), opening the body of a
locally closed tensor elimination by locally closed terms gives a locally closed term. -/
theorem casePair_lc_open₂ (h : (casePair t u).LC) (hs₁ : s₁.LC) (hs₂ : s₂.LC) :
    (u.open₂ s₁ s₂).LC := by
  classical
  cases h with
  | casePair L _ hu =>
    obtain ⟨x, hx⟩ := fresh_exists (L ∪ u.fv)
    obtain ⟨y, hy⟩ := fresh_exists (insert x (L ∪ u.fv ∪ s₁.fv))
    simp only [Finset.mem_insert, Finset.mem_union, not_or] at hx hy
    rw [open₂_eq_subst hx.2 hy.2.1.2 hy.1 hy.2.2 hs₁]
    exact subst_lc (subst_lc (hu x hx.1 y hy.2.1.1 (Ne.symm hy.1)) hs₁) hs₂

omit [DecidableEq Var] in
/-- When every finite set of names misses some name (`[HasFresh Var]`), opening the left branch of a
locally closed sum elimination by a locally closed term gives a locally closed term. -/
theorem casePlus_lc_open_left (h : (casePlus t u v).LC) (hs : s.LC) : (u ^ s).LC := by
  classical
  cases h with
  | casePlus L _ hu _ =>
    obtain ⟨x, hx⟩ := fresh_exists (L ∪ u.fv)
    rw [subst_intro (x := x) (fun hm => hx (Finset.mem_union_right _ hm))]
    exact subst_lc (hu x fun hm => hx (Finset.mem_union_left _ hm)) hs

omit [DecidableEq Var] in
/-- When every finite set of names misses some name (`[HasFresh Var]`), opening the right branch of
a locally closed sum elimination by a locally closed term gives a locally closed term. -/
theorem casePlus_lc_open_right (h : (casePlus t u v).LC) (hs : s.LC) : (v ^ s).LC := by
  classical
  cases h with
  | casePlus L _ _ hv =>
    obtain ⟨x, hx⟩ := fresh_exists (L ∪ v.fv)
    rw [subst_intro (x := x) (fun hm => hx (Finset.mem_union_right _ hm))]
    exact subst_lc (hv x fun hm => hx (Finset.mem_union_left _ hm)) hs

end Term

/-! ### Typing -/

variable {Var : Type u} {Base : Type v}

open Term Ty

/-- The linear typing judgment of section 2 of Pfenning's lecture notes on linear functional
programming (15-814, Lecture 19). The conclusion context of a rule with two context-disjoint
premises is any `Γ` with `Γ.Split Γ₁ Γ₂`. -/
inductive Typing : Context Var (Ty Base) → Term Var → Ty Base → Prop
  /-- Variable: the variable is the only hypothesis. -/
  | var {x : Var} {A : Ty Base} : Typing [⟨x, A⟩] (fvar x) A
  /-- `⊸`-introduction. -/
  | abs {Γ : Context Var (Ty Base)} {A B : Ty Base} {t : Term Var} (L : Finset Var) :
      (∀ x ∉ L, Typing (⟨x, A⟩ :: Γ) (t ^ fvar x) B) → Typing Γ (abs t) (lolli A B)
  /-- `⊸`-elimination: the context is partitioned. -/
  | app {Γ Γ₁ Γ₂ : Context Var (Ty Base)} {A B : Ty Base} {t s : Term Var} :
      Γ.Split Γ₁ Γ₂ → Typing Γ₁ t (lolli A B) → Typing Γ₂ s A → Typing Γ (app t s) B
  /-- `⊗`-introduction: the context is partitioned. -/
  | pair {Γ Γ₁ Γ₂ : Context Var (Ty Base)} {A B : Ty Base} {t s : Term Var} :
      Γ.Split Γ₁ Γ₂ → Typing Γ₁ t A → Typing Γ₂ s B → Typing Γ (pair t s) (tensor A B)
  /-- `⊗`-elimination: the context is partitioned; the body gains both components. -/
  | casePair {Γ Γ₁ Δ : Context Var (Ty Base)} {A B C : Ty Base} {t u : Term Var}
      (L : Finset Var) : Γ.Split Γ₁ Δ → Typing Γ₁ t (tensor A B) →
      (∀ x ∉ L, ∀ y ∉ L, x ≠ y →
        Typing (⟨y, B⟩ :: ⟨x, A⟩ :: Δ) (u.open₂ (fvar x) (fvar y)) C) →
      Typing Γ (casePair t u) C
  /-- `1`-introduction: the context is empty. -/
  | unit : Typing [] unit one
  /-- `1`-elimination: the context is partitioned. -/
  | caseUnit {Γ Γ₁ Δ : Context Var (Ty Base)} {C : Ty Base} {t u : Term Var} :
      Γ.Split Γ₁ Δ → Typing Γ₁ t one → Typing Δ u C → Typing Γ (caseUnit t u) C
  /-- `&`-introduction: both components share the context. -/
  | lpair {Γ : Context Var (Ty Base)} {A B : Ty Base} {t s : Term Var} :
      Typing Γ t A → Typing Γ s B → Typing Γ (lpair t s) (.with A B)
  /-- First `&`-elimination. -/
  | proj₁ {Γ : Context Var (Ty Base)} {A B : Ty Base} {t : Term Var} :
      Typing Γ t (.with A B) → Typing Γ (proj₁ t) A
  /-- Second `&`-elimination. -/
  | proj₂ {Γ : Context Var (Ty Base)} {A B : Ty Base} {t : Term Var} :
      Typing Γ t (.with A B) → Typing Γ (proj₂ t) B
  /-- Left `⊕`-introduction. -/
  | inl {Γ : Context Var (Ty Base)} {A B : Ty Base} {t : Term Var} :
      Typing Γ t A → Typing Γ (inl t) (oplus A B)
  /-- Right `⊕`-introduction. -/
  | inr {Γ : Context Var (Ty Base)} {A B : Ty Base} {t : Term Var} :
      Typing Γ t B → Typing Γ (inr t) (oplus A B)
  /-- `⊕`-elimination: the discriminant's context is separate; the branches share theirs. -/
  | casePlus {Γ Γ₁ Δ : Context Var (Ty Base)} {A B C : Ty Base} {t u v : Term Var}
      (L : Finset Var) : Γ.Split Γ₁ Δ → Typing Γ₁ t (oplus A B) →
      (∀ x ∉ L, Typing (⟨x, A⟩ :: Δ) (u ^ fvar x) C) →
      (∀ y ∉ L, Typing (⟨y, B⟩ :: Δ) (v ^ fvar y) C) → Typing Γ (casePlus t u v) C
  /-- `⊤`-introduction: any well-formed context is discarded. -/
  | lunit {Γ : Context Var (Ty Base)} : Γ✓ → Typing Γ lunit top
  /-- `0`-elimination: the context `Δ` beside the discriminant's is discarded. -/
  | caseZero {Γ Γ₁ Δ : Context Var (Ty Base)} {C : Ty Base} {t : Term Var} :
      Γ.Split Γ₁ Δ → Typing Γ₁ t zero → Typing Γ (caseZero t) C

@[inherit_doc]
scoped notation:50 Γ " ⊢ " t " ∶ " A:arg => Typing Γ t A

namespace Typing

variable {Γ Γ₁ Δ : Context Var (Ty Base)} {t u v s s₁ s₂ : Term Var} {A B C : Ty Base}
  {x y : Var} {i : ℕ}

/-! #### Structure -/

/-- Exchange: typing is invariant under permuting the context. -/
theorem perm (h : Γ ⊢ t ∶ A) (hp : Γ.Perm Δ) : Δ ⊢ t ∶ A := by
  induction h generalizing Δ with
  | var =>
    obtain rfl := List.perm_singleton.1 hp.symm
    exact Typing.var
  | unit =>
    obtain rfl := hp.nil_eq.symm
    exact Typing.unit
  | abs L _ ih => exact Typing.abs L fun x hx => ih x hx (hp.cons _)
  | app hs h₁ h₂ _ _ => exact Typing.app (hs.perm_whole hp) h₁ h₂
  | pair hs h₁ h₂ _ _ => exact Typing.pair (hs.perm_whole hp) h₁ h₂
  | casePair L hs ht hu _ _ => exact Typing.casePair L (hs.perm_whole hp) ht hu
  | caseUnit hs ht hu _ _ => exact Typing.caseUnit (hs.perm_whole hp) ht hu
  | lpair _ _ ih₁ ih₂ => exact Typing.lpair (ih₁ hp) (ih₂ hp)
  | proj₁ _ ih => exact Typing.proj₁ (ih hp)
  | proj₂ _ ih => exact Typing.proj₂ (ih hp)
  | inl _ ih => exact Typing.inl (ih hp)
  | inr _ ih => exact Typing.inr (ih hp)
  | casePlus L hs ht hu hv _ _ _ => exact Typing.casePlus L (hs.perm_whole hp) ht hu hv
  | lunit hwf => exact Typing.lunit ((List.perm_nodupKeys hp).1 hwf)
  | caseZero hs ht _ => exact Typing.caseZero (hs.perm_whole hp) ht

/-- Typed terms are locally closed. -/
theorem lc (h : Γ ⊢ t ∶ A) : t.LC := by
  induction h with
  | var => exact LC.fvar _
  | abs L _ ih => exact LC.abs L ih
  | app _ _ _ ih₁ ih₂ => exact LC.app ih₁ ih₂
  | pair _ _ _ ih₁ ih₂ => exact LC.pair ih₁ ih₂
  | casePair L _ _ _ iht ihu => exact LC.casePair L iht ihu
  | unit => exact LC.unit
  | caseUnit _ _ _ ih₁ ih₂ => exact LC.caseUnit ih₁ ih₂
  | lpair _ _ ih₁ ih₂ => exact LC.lpair ih₁ ih₂
  | proj₁ _ ih => exact LC.proj₁ ih
  | proj₂ _ ih => exact LC.proj₂ ih
  | inl _ ih => exact LC.inl ih
  | inr _ ih => exact LC.inr ih
  | casePlus L _ _ _ _ iht ihu ihv => exact LC.casePlus L iht ihu ihv
  | lunit _ => exact LC.lunit
  | caseZero _ _ ih => exact LC.caseZero ih

/-! #### Usage per rule: inversion -/

/-- A variable is typed exactly by the context holding only it. -/
theorem var_iff : Γ ⊢ fvar x ∶ A ↔ Γ = [⟨x, A⟩] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact Typing.var

/-- The multiplicative unit is typed only by the empty context, at type `1`. -/
theorem unit_iff : Γ ⊢ .unit ∶ A ↔ Γ = [] ∧ A = one := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact Typing.unit

/-- Inversion of abstraction. -/
theorem abs_iff : Γ ⊢ .abs t ∶ C ↔
    ∃ A B, C = lolli A B ∧ ∃ L : Finset Var, ∀ x ∉ L, ⟨x, A⟩ :: Γ ⊢ t ^ fvar x ∶ B := by
  constructor
  · intro h; cases h with | abs L h => exact ⟨_, _, rfl, L, h⟩
  · rintro ⟨A, B, rfl, L, h⟩; exact Typing.abs L h

/-- Application partitions the context. -/
theorem app_iff : Γ ⊢ .app t s ∶ B ↔
    ∃ A Γ₁ Γ₂, Γ.Split Γ₁ Γ₂ ∧ Γ₁ ⊢ t ∶ (lolli A B) ∧ Γ₂ ⊢ s ∶ A := by
  constructor
  · intro h; cases h with | app hs h₁ h₂ => exact ⟨_, _, _, hs, h₁, h₂⟩
  · rintro ⟨A, Γ₁, Γ₂, hs, h₁, h₂⟩; exact Typing.app hs h₁ h₂

/-- The tensor pair partitions the context. -/
theorem pair_iff : Γ ⊢ .pair t s ∶ C ↔
    ∃ A B Γ₁ Γ₂, C = tensor A B ∧ Γ.Split Γ₁ Γ₂ ∧ Γ₁ ⊢ t ∶ A ∧ Γ₂ ⊢ s ∶ B := by
  constructor
  · intro h; cases h with | pair hs h₁ h₂ => exact ⟨_, _, _, _, rfl, hs, h₁, h₂⟩
  · rintro ⟨A, B, Γ₁, Γ₂, rfl, hs, h₁, h₂⟩; exact Typing.pair hs h₁ h₂

/-- Tensor elimination partitions the context. -/
theorem casePair_iff : Γ ⊢ .casePair t u ∶ C ↔
    ∃ A B Γ₁ Δ, Γ.Split Γ₁ Δ ∧ Γ₁ ⊢ t ∶ (tensor A B) ∧ ∃ L : Finset Var,
      ∀ x ∉ L, ∀ y ∉ L, x ≠ y → ⟨y, B⟩ :: ⟨x, A⟩ :: Δ ⊢ u.open₂ (fvar x) (fvar y) ∶ C :=
  by
    constructor
    · intro h; cases h with | casePair L hs ht hu => exact ⟨_, _, _, _, hs, ht, L, hu⟩
    · rintro ⟨A, B, Γ₁, Δ, hs, ht, L, hu⟩; exact Typing.casePair L hs ht hu

/-- Elimination of the multiplicative unit partitions the context. -/
theorem caseUnit_iff : Γ ⊢ .caseUnit t u ∶ C ↔
    ∃ Γ₁ Δ, Γ.Split Γ₁ Δ ∧ Γ₁ ⊢ t ∶ one ∧ Δ ⊢ u ∶ C := by
  constructor
  · intro h; cases h with | caseUnit hs ht hu => exact ⟨_, _, hs, ht, hu⟩
  · rintro ⟨Γ₁, Δ, hs, ht, hu⟩; exact Typing.caseUnit hs ht hu

/-- The additive pair shares the context. -/
theorem lpair_iff : Γ ⊢ .lpair t s ∶ C ↔
    ∃ A B, C = .with A B ∧ Γ ⊢ t ∶ A ∧ Γ ⊢ s ∶ B := by
  constructor
  · intro h; cases h with | lpair h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩
  · rintro ⟨A, B, rfl, h₁, h₂⟩; exact Typing.lpair h₁ h₂

/-- Inversion of the first projection. -/
theorem proj₁_iff : Γ ⊢ .proj₁ t ∶ A ↔ ∃ B, Γ ⊢ t ∶ (.with A B) := by
  constructor
  · intro h; cases h with | proj₁ h => exact ⟨_, h⟩
  · rintro ⟨B, h⟩; exact Typing.proj₁ h

/-- Inversion of the second projection. -/
theorem proj₂_iff : Γ ⊢ .proj₂ t ∶ B ↔ ∃ A, Γ ⊢ t ∶ (.with A B) := by
  constructor
  · intro h; cases h with | proj₂ h => exact ⟨_, h⟩
  · rintro ⟨A, h⟩; exact Typing.proj₂ h

/-- Inversion of the left injection. -/
theorem inl_iff : Γ ⊢ .inl t ∶ C ↔ ∃ A B, C = oplus A B ∧ Γ ⊢ t ∶ A := by
  constructor
  · intro h; cases h with | inl h => exact ⟨_, _, rfl, h⟩
  · rintro ⟨A, B, rfl, h⟩; exact Typing.inl h

/-- Inversion of the right injection. -/
theorem inr_iff : Γ ⊢ .inr t ∶ C ↔ ∃ A B, C = oplus A B ∧ Γ ⊢ t ∶ B := by
  constructor
  · intro h; cases h with | inr h => exact ⟨_, _, rfl, h⟩
  · rintro ⟨A, B, rfl, h⟩; exact Typing.inr h

/-- Sum elimination separates the discriminant's context and shares the branches'. -/
theorem casePlus_iff : Γ ⊢ .casePlus t u v ∶ C ↔
    ∃ A B Γ₁ Δ, Γ.Split Γ₁ Δ ∧ Γ₁ ⊢ t ∶ (oplus A B) ∧ ∃ L : Finset Var,
      (∀ x ∉ L, ⟨x, A⟩ :: Δ ⊢ u ^ fvar x ∶ C) ∧ (∀ y ∉ L, ⟨y, B⟩ :: Δ ⊢ v ^ fvar y ∶ C) :=
  by
    constructor
    · intro h; cases h with | casePlus L hs ht hu hv => exact ⟨_, _, _, _, hs, ht, L, hu, hv⟩
    · rintro ⟨A, B, Γ₁, Δ, hs, ht, L, hu, hv⟩; exact Typing.casePlus L hs ht hu hv

/-- The additive unit discards any well-formed context. -/
theorem lunit_iff : Γ ⊢ .lunit ∶ A ↔ A = top ∧ Γ✓ := by
  constructor
  · intro h; cases h with | lunit hwf => exact ⟨rfl, hwf⟩
  · rintro ⟨rfl, hwf⟩; exact Typing.lunit hwf

/-- Zero elimination discards the context beside the discriminant's. -/
theorem caseZero_iff : Γ ⊢ .caseZero t ∶ C ↔ ∃ Γ₁ Δ, Γ.Split Γ₁ Δ ∧ Γ₁ ⊢ t ∶ zero := by
  constructor
  · intro h; cases h with | caseZero hs ht => exact ⟨_, _, hs, ht⟩
  · rintro ⟨Γ₁, Δ, hs, ht⟩; exact Typing.caseZero hs ht

/-! #### Usage: free variables -/

variable [HasFresh Var]

/-- When every finite set of names misses some name (`[HasFresh Var]`), the context of a typed term
is well formed. -/
theorem wf (h : Γ ⊢ t ∶ A) : Γ✓ := by
  induction h with
  | var => exact List.nodupKeys_singleton _
  | abs L _ ih =>
    obtain ⟨x, hx⟩ := fresh_exists L
    exact (List.nodupKeys_cons.1 (ih x hx)).2
  | unit => exact List.nodupKeys_nil
  | lunit hwf => exact hwf
  | app hs _ _ _ _ => exact hs.wf
  | pair hs _ _ _ _ => exact hs.wf
  | casePair _ hs _ _ _ _ => exact hs.wf
  | caseUnit hs _ _ _ _ => exact hs.wf
  | casePlus _ hs _ _ _ _ _ _ => exact hs.wf
  | caseZero hs _ _ => exact hs.wf
  | lpair _ _ ih _ => exact ih
  | proj₁ _ ih => exact ih
  | proj₂ _ ih => exact ih
  | inl _ ih => exact ih
  | inr _ ih => exact ih

variable [DecidableEq Var]

omit [HasFresh Var] in
/-- The domain of a context extended by one hypothesis. -/
private theorem dom_cons : Context.dom (⟨x, A⟩ :: Γ) = insert x Γ.dom := by
  simp [Context.dom]

/-- A body whose fresh double openings have free variables in their contexts. -/
private theorem casePair_body_fv {L : Finset Var}
    (ih : ∀ x ∉ L, ∀ y ∉ L, x ≠ y →
      (u.open₂ (fvar x) (fvar y)).fv ⊆ Context.dom (⟨y, B⟩ :: ⟨x, A⟩ :: Δ)) :
    u.fv ⊆ Δ.dom :=
  Term.fv_subset_of_open₂ fun x hx y hy hxy => by
    simpa [dom_cons] using ih x hx y hy hxy

/-- When every finite set of names misses some name (`[HasFresh Var]`), every free variable of a
typed term is a hypothesis. -/
theorem fv_subset_dom (h : Γ ⊢ t ∶ A) : t.fv ⊆ Γ.dom := by
  induction h with
  | var => simp [fv, Context.dom]
  | abs L _ ih =>
    simp only [fv]
    exact Term.fv_subset_of_open fun x hx => by simpa [dom_cons] using ih x hx
  | app hs _ _ ih₁ ih₂ => rw [hs.dom_eq]; exact Finset.union_subset_union ih₁ ih₂
  | pair hs _ _ ih₁ ih₂ => rw [hs.dom_eq]; exact Finset.union_subset_union ih₁ ih₂
  | casePair L hs _ hu ih₁ ih₂ =>
    rw [hs.dom_eq]; exact Finset.union_subset_union ih₁ (casePair_body_fv ih₂)
  | unit => simp [fv]
  | caseUnit hs _ _ ih₁ ih₂ => rw [hs.dom_eq]; exact Finset.union_subset_union ih₁ ih₂
  | lpair _ _ ih₁ ih₂ => exact Finset.union_subset ih₁ ih₂
  | proj₁ _ ih => exact ih
  | proj₂ _ ih => exact ih
  | inl _ ih => exact ih
  | inr _ ih => exact ih
  | casePlus L hs _ _ _ iht ihu ihv =>
    rw [hs.dom_eq]
    refine Finset.union_subset (Finset.union_subset_union iht ?_) ?_
    · exact Term.fv_subset_of_open fun x hx => by simpa [dom_cons] using ihu x hx
    · exact (Term.fv_subset_of_open fun x hx => by simpa [dom_cons] using ihv x hx).trans
        Finset.subset_union_right
  | lunit _ => simp [fv]
  | caseZero hs _ ih => rw [hs.dom_eq]; exact ih.trans Finset.subset_union_left

/-- When every finite set of names misses some name (`[HasFresh Var]`), every hypothesis is used by
a typed term that discards nothing. -/
theorem dom_subset_fv (h : Γ ⊢ t ∶ A) (ht : t.NoDiscard) : Γ.dom ⊆ t.fv := by
  revert ht
  induction h with
  | var => intro _; simp [fv, Context.dom]
  | abs L _ ih =>
    intro ht
    simp only [fv]
    exact Term.subset_fv_of_open fun x hx => by
      simpa [dom_cons] using ih x hx (Term.noDiscard_openRec_fvar 0 ht)
  | app hs _ _ ih₁ ih₂ =>
    intro ht; rw [hs.dom_eq]; exact Finset.union_subset_union (ih₁ ht.1) (ih₂ ht.2)
  | pair hs _ _ ih₁ ih₂ =>
    intro ht; rw [hs.dom_eq]; exact Finset.union_subset_union (ih₁ ht.1) (ih₂ ht.2)
  | casePair L hs _ _ ih₁ ih₂ =>
    intro ht
    rw [hs.dom_eq]
    refine Finset.union_subset_union (ih₁ ht.1)
      (Term.subset_fv_of_open₂ (L := L) fun x hx y hy hxy => ?_)
    simpa [dom_cons] using
      ih₂ x hx y hy hxy (Term.noDiscard_openRec_fvar 0 (Term.noDiscard_openRec_fvar 1 ht.2))
  | unit => intro _; simp [Context.dom]
  | caseUnit hs _ _ ih₁ ih₂ =>
    intro ht; rw [hs.dom_eq]; exact Finset.union_subset_union (ih₁ ht.1) (ih₂ ht.2)
  | lpair _ _ ih₁ _ => intro ht; exact (ih₁ ht.1).trans Finset.subset_union_left
  | proj₁ _ ih => exact ih
  | proj₂ _ ih => exact ih
  | inl _ ih => exact ih
  | inr _ ih => exact ih
  | casePlus L hs _ _ _ iht ihu _ =>
    intro ht
    rw [hs.dom_eq]
    simp only [fv]
    refine Finset.union_subset ((iht ht.1).trans
      (Finset.subset_union_left.trans Finset.subset_union_left)) ?_
    refine Finset.Subset.trans ?_ (Finset.subset_union_right.trans Finset.subset_union_left)
    exact Term.subset_fv_of_open fun x hx => by
      simpa [dom_cons] using ihu x hx (Term.noDiscard_openRec_fvar 0 ht.2.1)
  | lunit _ => intro ht; exact ht.elim
  | caseZero _ _ _ => intro ht; exact ht.elim

/-- When every finite set of names misses some name (`[HasFresh Var]`), the function and the
argument of a typed application have disjoint free variables. -/
theorem app_fv_disjoint (h : Γ ⊢ .app t s ∶ B) : Disjoint t.fv s.fv := by
  obtain ⟨A, Γ₁, Γ₂, hs, h₁, h₂⟩ := app_iff.1 h
  exact Disjoint.mono h₁.fv_subset_dom h₂.fv_subset_dom hs.disjoint

/-- When every finite set of names misses some name (`[HasFresh Var]`), the components of a typed
tensor pair have disjoint free variables. -/
theorem pair_fv_disjoint (h : Γ ⊢ .pair t s ∶ C) : Disjoint t.fv s.fv := by
  obtain ⟨A, B, Γ₁, Γ₂, -, hs, h₁, h₂⟩ := pair_iff.1 h
  exact Disjoint.mono h₁.fv_subset_dom h₂.fv_subset_dom hs.disjoint

/-- When every finite set of names misses some name (`[HasFresh Var]`), the discriminant and the
body of a typed tensor elimination have disjoint free variables. -/
theorem casePair_fv_disjoint (h : Γ ⊢ .casePair t u ∶ C) : Disjoint t.fv u.fv := by
  obtain ⟨A, B, Γ₁, Δ, hs, ht, L, hu⟩ := casePair_iff.1 h
  exact Disjoint.mono ht.fv_subset_dom
    (casePair_body_fv fun x hx y hy hxy => (hu x hx y hy hxy).fv_subset_dom) hs.disjoint

/-- When every finite set of names misses some name (`[HasFresh Var]`), the discriminant and the
body of a typed unit elimination have disjoint free variables. -/
theorem caseUnit_fv_disjoint (h : Γ ⊢ .caseUnit t u ∶ C) : Disjoint t.fv u.fv := by
  obtain ⟨Γ₁, Δ, hs, ht, hu⟩ := caseUnit_iff.1 h
  exact Disjoint.mono ht.fv_subset_dom hu.fv_subset_dom hs.disjoint

/-- When every finite set of names misses some name (`[HasFresh Var]`), the discriminant of a typed
sum elimination shares no free variable with the branches. -/
theorem casePlus_fv_disjoint (h : Γ ⊢ .casePlus t u v ∶ C) : Disjoint t.fv (u.fv ∪ v.fv) :=
  by
    obtain ⟨A, B, Γ₁, Δ, hs, ht, L, hu, hv⟩ := casePlus_iff.1 h
    refine Disjoint.mono ht.fv_subset_dom (Finset.union_subset ?_ ?_) hs.disjoint
    · exact Term.fv_subset_of_open fun x hx => by simpa [dom_cons] using (hu x hx).fv_subset_dom
    · exact Term.fv_subset_of_open fun x hx => by simpa [dom_cons] using (hv x hx).fv_subset_dom

/-- When every finite set of names misses some name (`[HasFresh Var]`), the components of a typed
additive pair that discard nothing have the same free variables. -/
theorem lpair_fv_eq (h : Γ ⊢ .lpair t s ∶ C) (ht : t.NoDiscard) (hs : s.NoDiscard) :
    t.fv = s.fv := by
  obtain ⟨A', B', -, h₁, h₂⟩ := lpair_iff.1 h
  exact (Finset.Subset.antisymm h₁.fv_subset_dom (h₁.dom_subset_fv ht)).trans
    (Finset.Subset.antisymm h₂.fv_subset_dom (h₂.dom_subset_fv hs)).symm

/-- When every finite set of names misses some name (`[HasFresh Var]`), the branches of a typed sum
elimination that discard nothing have the same free variables. -/
theorem casePlus_fv_eq (h : Γ ⊢ .casePlus t u v ∶ C) (hu : u.NoDiscard) (hv : v.NoDiscard) :
    u.fv = v.fv := by
  obtain ⟨A, B, Γ₁, Δ, hs, ht, L, hu', hv'⟩ := casePlus_iff.1 h
  have eu : u.fv = Δ.dom := Finset.Subset.antisymm
    (Term.fv_subset_of_open fun x hx => by simpa [dom_cons] using (hu' x hx).fv_subset_dom)
    (Term.subset_fv_of_open fun x hx => by
      simpa [dom_cons] using (hu' x hx).dom_subset_fv (Term.noDiscard_openRec_fvar 0 hu))
  have ev : v.fv = Δ.dom := Finset.Subset.antisymm
    (Term.fv_subset_of_open fun x hx => by simpa [dom_cons] using (hv' x hx).fv_subset_dom)
    (Term.subset_fv_of_open fun x hx => by
      simpa [dom_cons] using (hv' x hx).dom_subset_fv (Term.noDiscard_openRec_fvar 0 hv))
  rw [eu, ev]

/-! #### Exactly once -/

/-- When every finite set of names misses some name (`[HasFresh Var]`), a typed term of the
multiplicative fragment uses each hypothesis exactly once. -/
theorem occ_eq_one (h : Γ ⊢ t ∶ A) (ht : t.Multiplicative) (hx : x ∈ Γ.dom) : t.occ x = 1 :=
  by
    revert ht hx
    induction h generalizing x with
    | var => intro _ hx; simp_all [Context.dom, occ]
    | abs L _ ih =>
      intro ht hx
      obtain ⟨z, hz⟩ := fresh_exists (insert x L)
      simp only [Finset.mem_insert, not_or] at hz
      have := @ih z hz.2 x (Term.multiplicative_openRec_fvar 0 ht)
        (by rw [dom_cons]; exact Finset.mem_insert_of_mem hx)
      rw [Term.open', Term.occ_openRec_fvar 0 (Ne.symm hz.1)] at this
      exact this
    | app hs h₁ h₂ ih₁ ih₂ =>
      intro ht hx
      simp only [occ]
      rcases Finset.mem_union.1 (hs.dom_eq ▸ hx) with hx | hx
      · rw [ih₁ ht.1 hx, occ_eq_zero_iff.2 fun hm =>
          Finset.disjoint_left.1 hs.disjoint hx (h₂.fv_subset_dom hm)]
      · rw [ih₂ ht.2 hx, occ_eq_zero_iff.2 fun hm =>
          Finset.disjoint_right.1 hs.disjoint hx (h₁.fv_subset_dom hm)]
    | pair hs h₁ h₂ ih₁ ih₂ =>
      intro ht hx
      simp only [occ]
      rcases Finset.mem_union.1 (hs.dom_eq ▸ hx) with hx | hx
      · rw [ih₁ ht.1 hx, occ_eq_zero_iff.2 fun hm =>
          Finset.disjoint_left.1 hs.disjoint hx (h₂.fv_subset_dom hm)]
      · rw [ih₂ ht.2 hx, occ_eq_zero_iff.2 fun hm =>
          Finset.disjoint_right.1 hs.disjoint hx (h₁.fv_subset_dom hm)]
    | casePair L hs h₁ hu ih₁ ih₂ =>
      intro ht hx
      simp only [occ]
      have hfu := casePair_body_fv fun x hx y hy hxy => (hu x hx y hy hxy).fv_subset_dom
      rcases Finset.mem_union.1 (hs.dom_eq ▸ hx) with hx | hx
      · rw [ih₁ ht.1 hx, occ_eq_zero_iff.2 fun hm =>
          Finset.disjoint_left.1 hs.disjoint hx (hfu hm)]
      · obtain ⟨z, hz⟩ := fresh_exists (insert x L)
        obtain ⟨w, hw⟩ := fresh_exists (insert z (insert x L))
        simp only [Finset.mem_insert, not_or] at hz hw
        have := @ih₂ z hz.2 w hw.2.2 (Ne.symm hw.1) x
          (Term.multiplicative_openRec_fvar 0 (Term.multiplicative_openRec_fvar 1 ht.2))
          (by rw [dom_cons, dom_cons]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
        rw [Term.open₂, Term.occ_openRec_fvar 0 (Ne.symm hw.2.1),
          Term.occ_openRec_fvar 1 (Ne.symm hz.1)] at this
        rw [this, occ_eq_zero_iff.2 fun hm =>
          Finset.disjoint_right.1 hs.disjoint hx (h₁.fv_subset_dom hm)]
    | unit => intro _ hx; simp [Context.dom] at hx
    | caseUnit hs h₁ h₂ ih₁ ih₂ =>
      intro ht hx
      simp only [occ]
      rcases Finset.mem_union.1 (hs.dom_eq ▸ hx) with hx | hx
      · rw [ih₁ ht.1 hx, occ_eq_zero_iff.2 fun hm =>
          Finset.disjoint_left.1 hs.disjoint hx (h₂.fv_subset_dom hm)]
      · rw [ih₂ ht.2 hx, occ_eq_zero_iff.2 fun hm =>
          Finset.disjoint_right.1 hs.disjoint hx (h₁.fv_subset_dom hm)]
    | lpair => intro ht; exact ht.elim
    | proj₁ => intro ht; exact ht.elim
    | proj₂ => intro ht; exact ht.elim
    | inl => intro ht; exact ht.elim
    | inr => intro ht; exact ht.elim
    | casePlus => intro ht; exact ht.elim
    | lunit => intro ht; exact ht.elim
    | caseZero => intro ht; exact ht.elim

/-- When every finite set of names misses some name (`[HasFresh Var]`), a typed term does not
mention names outside its context. -/
theorem occ_eq_zero (h : Γ ⊢ t ∶ A) (hx : x ∉ Γ.dom) : t.occ x = 0 :=
  occ_eq_zero_iff.2 fun hm => hx (h.fv_subset_dom hm)

/-! #### Linear substitution -/

omit [HasFresh Var] [DecidableEq Var] in
/-- Locating a hypothesis of a split context in one of its parts. -/
private theorem split_locate {Θ Θ₁ Θ₂ : Context Var (Ty Base)} (hs : Θ.Split Θ₁ Θ₂)
    (hp : Θ.Perm (⟨x, A⟩ :: Δ)) :
    (∃ Δ₁, Θ₁.Perm (⟨x, A⟩ :: Δ₁) ∧ Δ.Perm (Δ₁ ++ Θ₂) ∧ x ∉ Θ₂.keys) ∨
      (∃ Δ₂, Θ₂.Perm (⟨x, A⟩ :: Δ₂) ∧ Δ.Perm (Θ₁ ++ Δ₂) ∧ x ∉ Θ₁.keys) := by
  have hmem : (⟨x, A⟩ : (_ : Var) × Ty Base) ∈ Θ₁ ++ Θ₂ :=
    hs.perm.subset (hp.symm.subset List.mem_cons_self)
  have hk : (Θ₁.keys ++ Θ₂.keys).Nodup := by
    simpa [HasWellFormed.wf, List.NodupKeys, List.keys_append] using hs.wf_append
  rcases List.mem_append.1 hmem with h | h
  · obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem h
    refine Or.inl ⟨l₁ ++ l₂, List.perm_middle, ?_, ?_⟩
    · refine (List.Perm.cons_inv (a := ⟨x, A⟩) ?_)
      refine hp.symm.trans (hs.perm.trans ?_)
      exact List.perm_middle.append_right Θ₂
    · exact List.disjoint_of_nodup_append hk (List.mem_keys_of_mem h)
  · obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem h
    refine Or.inr ⟨l₁ ++ l₂, List.perm_middle, ?_, ?_⟩
    · refine (List.Perm.cons_inv (a := ⟨x, A⟩) ?_)
      refine hp.symm.trans (hs.perm.trans ?_)
      exact (List.perm_middle.append_left Θ₁).trans List.perm_middle
    · exact fun hx => List.disjoint_of_nodup_append hk hx (List.mem_keys_of_mem h)

omit [HasFresh Var] [DecidableEq Var] in
/-- The substituted context splits off the left part's remainder. -/
private theorem split_subst_left {Δ₁ Θ₂ : Context Var (Ty Base)} (hwf : (Γ ++ Δ)✓)
    (hΔ : Δ.Perm (Δ₁ ++ Θ₂)) : (Γ ++ Δ).Split (Γ ++ Δ₁) Θ₂ ∧ (Γ ++ Δ₁)✓ := by
  have hp : (Γ ++ Δ).Perm ((Γ ++ Δ₁) ++ Θ₂) := by
    rw [List.append_assoc]; exact hΔ.append_left Γ
  exact ⟨⟨hwf, hp⟩, List.NodupKeys.sublist (List.sublist_append_left _ _)
    ((List.perm_nodupKeys hp).1 hwf)⟩

omit [HasFresh Var] [DecidableEq Var] in
/-- The substituted context splits off the right part's remainder. -/
private theorem split_subst_right {Θ₁ Δ₂ : Context Var (Ty Base)} (hwf : (Γ ++ Δ)✓)
    (hΔ : Δ.Perm (Θ₁ ++ Δ₂)) : (Γ ++ Δ).Split Θ₁ (Γ ++ Δ₂) ∧ (Γ ++ Δ₂)✓ := by
  have hp : (Γ ++ Δ).Perm (Θ₁ ++ (Γ ++ Δ₂)) := by
    refine (hΔ.append_left Γ).trans ?_
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := Γ) (l₂ := Θ₁)).append_right Δ₂
  exact ⟨⟨hwf, hp⟩, List.NodupKeys.sublist (List.sublist_append_right _ _)
    ((List.perm_nodupKeys hp).1 hwf)⟩

omit [HasFresh Var] in
/-- A fresh hypothesis inserted in the middle keeps a context well formed. -/
private theorem wf_middle {z : Var} {D : Ty Base} (hwf : (Γ ++ Δ)✓) (hz : z ∉ (Γ ++ Δ).dom) :
    (Γ ++ ⟨z, D⟩ :: Δ)✓ :=
  List.nodupKeys_middle.2 (List.nodupKeys_cons.2 ⟨by simpa [Context.dom] using hz, hwf⟩)

/-- Linear substitution for a context given up to permutation. -/
private theorem subst_aux (hs : Γ ⊢ s ∶ A) {Θ : Context Var (Ty Base)} {B' : Ty Base}
    (ht : Θ ⊢ t ∶ B') :
    ∀ {Δ : Context Var (Ty Base)}, Θ.Perm (⟨x, A⟩ :: Δ) → (Γ ++ Δ)✓ → Γ ++ Δ ⊢ t[x := s] ∶ B' := by
  have hslc := hs.lc
  induction ht with
  | @var y D =>
    intro Δ hp hwf
    obtain rfl : Δ = [] := List.eq_nil_of_length_eq_zero (by simpa using hp.length_eq.symm)
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 (List.singleton_perm_singleton.1 hp)
    obtain rfl := eq_of_heq h
    simpa [subst_eq, subst] using hs
  | @abs Θ A' B'' t L _ ih =>
    intro Δ hp hwf
    simp only [subst_eq, Term.subst]
    refine Typing.abs (L ∪ {x} ∪ (Γ ++ Δ).dom) fun z hz => ?_
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hz
    have := ih z hz.1.1 ((hp.cons _).trans (List.Perm.swap _ _ _)) (wf_middle hwf hz.2)
    rw [subst_open_var hz.1.2 hslc] at this
    exact this.perm List.perm_middle
  | app hsp h₁ h₂ ih₁ ih₂ =>
    intro Δ hp hwf
    simp only [subst_eq, Term.subst]
    rcases split_locate hsp hp with ⟨Δ₁, hp₁, hΔ, hx⟩ | ⟨Δ₂, hp₂, hΔ, hx⟩
    · obtain ⟨hs', hwf'⟩ := split_subst_left hwf hΔ
      have e := subst_fresh (s := s) fun hm => hx (by simpa [Context.dom] using h₂.fv_subset_dom hm)
      rw [subst_eq] at e; rw [e]
      exact Typing.app hs' (ih₁ hp₁ hwf') h₂
    · obtain ⟨hs', hwf'⟩ := split_subst_right hwf hΔ
      have e := subst_fresh (s := s) fun hm => hx (by simpa [Context.dom] using h₁.fv_subset_dom hm)
      rw [subst_eq] at e; rw [e]
      exact Typing.app hs' h₁ (ih₂ hp₂ hwf')
  | pair hsp h₁ h₂ ih₁ ih₂ =>
    intro Δ hp hwf
    simp only [subst_eq, Term.subst]
    rcases split_locate hsp hp with ⟨Δ₁, hp₁, hΔ, hx⟩ | ⟨Δ₂, hp₂, hΔ, hx⟩
    · obtain ⟨hs', hwf'⟩ := split_subst_left hwf hΔ
      have e := subst_fresh (s := s) fun hm => hx (by simpa [Context.dom] using h₂.fv_subset_dom hm)
      rw [subst_eq] at e; rw [e]
      exact Typing.pair hs' (ih₁ hp₁ hwf') h₂
    · obtain ⟨hs', hwf'⟩ := split_subst_right hwf hΔ
      have e := subst_fresh (s := s) fun hm => hx (by simpa [Context.dom] using h₁.fv_subset_dom hm)
      rw [subst_eq] at e; rw [e]
      exact Typing.pair hs' h₁ (ih₂ hp₂ hwf')
  | caseUnit hsp h₁ h₂ ih₁ ih₂ =>
    intro Δ hp hwf
    simp only [subst_eq, Term.subst]
    rcases split_locate hsp hp with ⟨Δ₁, hp₁, hΔ, hx⟩ | ⟨Δ₂, hp₂, hΔ, hx⟩
    · obtain ⟨hs', hwf'⟩ := split_subst_left hwf hΔ
      have e := subst_fresh (s := s) fun hm => hx (by simpa [Context.dom] using h₂.fv_subset_dom hm)
      rw [subst_eq] at e; rw [e]
      exact Typing.caseUnit hs' (ih₁ hp₁ hwf') h₂
    · obtain ⟨hs', hwf'⟩ := split_subst_right hwf hΔ
      have e := subst_fresh (s := s) fun hm => hx (by simpa [Context.dom] using h₁.fv_subset_dom hm)
      rw [subst_eq] at e; rw [e]
      exact Typing.caseUnit hs' h₁ (ih₂ hp₂ hwf')
  | @casePair Θ Θ₁ Δb A' B'' C' t u L hsp h₁ hu ih₁ ih₂ =>
    intro Δ hp hwf
    simp only [subst_eq, Term.subst]
    rcases split_locate hsp hp with ⟨Δ₁, hp₁, hΔ, hx⟩ | ⟨Δ₂, hp₂, hΔ, hx⟩
    · obtain ⟨hs', hwf'⟩ := split_subst_left hwf hΔ
      have hfu := casePair_body_fv fun z hz w hw hzw => (hu z hz w hw hzw).fv_subset_dom
      have e := subst_fresh (s := s) fun hm => hx (by simpa [Context.dom] using hfu hm)
      rw [subst_eq] at e; rw [e]
      exact Typing.casePair L hs' (ih₁ hp₁ hwf') hu
    · obtain ⟨hs', hwf'⟩ := split_subst_right hwf hΔ
      have e := subst_fresh (s := s) fun hm => hx (by simpa [Context.dom] using h₁.fv_subset_dom hm)
      rw [subst_eq] at e; rw [e]
      refine Typing.casePair (L ∪ {x} ∪ (Γ ++ Δ₂).dom) hs' h₁ fun z hz w hw hzw => ?_
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hz hw
      have hwf'' : (Γ ++ ⟨w, B''⟩ :: ⟨z, A'⟩ :: Δ₂)✓ :=
        wf_middle (wf_middle hwf' hz.2) (by
          simp only [Context.dom, List.keys_append, List.keys_cons, List.mem_toFinset,
            List.mem_append, List.mem_cons, not_or] at hw ⊢
          exact ⟨hw.2.1, Ne.symm hzw, hw.2.2⟩)
      have hp' : (⟨w, B''⟩ :: ⟨z, A'⟩ :: Δb).Perm (⟨x, A⟩ :: ⟨w, B''⟩ :: ⟨z, A'⟩ :: Δ₂) :=
        ((hp₂.cons _).cons _).trans
          (((List.Perm.swap ⟨x, A⟩ ⟨z, A'⟩ Δ₂).cons ⟨w, B''⟩).trans
            (List.Perm.swap ⟨x, A⟩ ⟨w, B''⟩ (⟨z, A'⟩ :: Δ₂)))
      have := ih₂ z hz.1.1 w hw.1.1 hzw hp' hwf''
      rw [subst_open₂_var hz.1.2 hw.1.2 hslc] at this
      exact this.perm (List.perm_middle.trans (List.perm_middle.cons _))
  | unit => intro Δ hp _; exact absurd hp.length_eq (by simp)
  | lpair _ _ ih₁ ih₂ =>
    intro Δ hp hwf
    exact Typing.lpair (ih₁ hp hwf) (ih₂ hp hwf)
  | proj₁ _ ih => intro Δ hp hwf; exact Typing.proj₁ (ih hp hwf)
  | proj₂ _ ih => intro Δ hp hwf; exact Typing.proj₂ (ih hp hwf)
  | inl _ ih => intro Δ hp hwf; exact Typing.inl (ih hp hwf)
  | inr _ ih => intro Δ hp hwf; exact Typing.inr (ih hp hwf)
  | @casePlus Θ Θ₁ Δb A' B'' C' t u v L hsp h₁ hu hv ih₁ ihu ihv =>
    intro Δ hp hwf
    simp only [subst_eq, Term.subst]
    rcases split_locate hsp hp with ⟨Δ₁, hp₁, hΔ, hx⟩ | ⟨Δ₂, hp₂, hΔ, hx⟩
    · obtain ⟨hs', hwf'⟩ := split_subst_left hwf hΔ
      have hfu : u.fv ⊆ Δb.dom := Term.fv_subset_of_open fun z hz => by
        simpa [dom_cons] using (hu z hz).fv_subset_dom
      have hfv : v.fv ⊆ Δb.dom := Term.fv_subset_of_open fun z hz => by
        simpa [dom_cons] using (hv z hz).fv_subset_dom
      have eu := subst_fresh (s := s) fun hm => hx (by simpa [Context.dom] using hfu hm)
      have ev := subst_fresh (s := s) fun hm => hx (by simpa [Context.dom] using hfv hm)
      rw [subst_eq] at eu ev; rw [eu, ev]
      exact Typing.casePlus L hs' (ih₁ hp₁ hwf') hu hv
    · obtain ⟨hs', hwf'⟩ := split_subst_right hwf hΔ
      have e := subst_fresh (s := s) fun hm => hx (by simpa [Context.dom] using h₁.fv_subset_dom hm)
      rw [subst_eq] at e; rw [e]
      refine Typing.casePlus (L ∪ {x} ∪ (Γ ++ Δ₂).dom) hs' h₁ (fun z hz => ?_) (fun z hz => ?_)
      · simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hz
        have := ihu z hz.1.1 ((hp₂.cons _).trans (List.Perm.swap _ _ _)) (wf_middle hwf' hz.2)
        rw [subst_open_var hz.1.2 hslc] at this
        exact this.perm List.perm_middle
      · simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hz
        have := ihv z hz.1.1 ((hp₂.cons _).trans (List.Perm.swap _ _ _)) (wf_middle hwf' hz.2)
        rw [subst_open_var hz.1.2 hslc] at this
        exact this.perm List.perm_middle
  | lunit _ =>
    intro Δ _ hwf
    exact Typing.lunit hwf
  | caseZero hsp h₁ ih₁ =>
    intro Δ hp hwf
    simp only [subst_eq, Term.subst]
    rcases split_locate hsp hp with ⟨Δ₁, hp₁, hΔ, hx⟩ | ⟨Δ₂, hp₂, hΔ, hx⟩
    · obtain ⟨hs', hwf'⟩ := split_subst_left hwf hΔ
      exact Typing.caseZero hs' (ih₁ hp₁ hwf')
    · obtain ⟨hs', hwf'⟩ := split_subst_right hwf hΔ
      have e := subst_fresh (s := s) fun hm => hx (by simpa [Context.dom] using h₁.fv_subset_dom hm)
      rw [subst_eq] at e; rw [e]
      exact Typing.caseZero hs' h₁

/-- **Linear substitution** (Property 1 of Pfenning's lecture notes on linear functional
programming, 15-814, Lecture 19): when every finite set of names misses some name
(`[HasFresh Var]`), if `Γ ⊢ s ∶ A` and `Δ, x : A ⊢ t ∶ B` with `Γ` and `Δ` disjoint, then
`Γ, Δ ⊢ t[x := s] ∶ B`. -/
theorem subst (hs : Γ ⊢ s ∶ A) (ht : ⟨x, A⟩ :: Δ ⊢ t ∶ B) (hwf : (Γ ++ Δ)✓) :
    Γ ++ Δ ⊢ t[x := s] ∶ B := subst_aux hs ht (List.Perm.refl _) hwf

omit [DecidableEq Var] in
/-- Linear substitution into a body opened by one fresh name, as in a β-step. When every finite set
of names misses some name (`[HasFresh Var]`): if `Δ, x : A ⊢ t ^ fvar x ∶ B` for every name `x`
outside a finite set, `Γ ⊢ s ∶ A`, and `Γ` and `Δ` are disjoint, then `Γ, Δ ⊢ t ^ s ∶ B`. -/
theorem open_subst {L : Finset Var} (ht : ∀ x ∉ L, ⟨x, A⟩ :: Δ ⊢ t ^ fvar x ∶ B)
    (hs : Γ ⊢ s ∶ A) (hwf : (Γ ++ Δ)✓) : Γ ++ Δ ⊢ t ^ s ∶ B := by
  classical
  obtain ⟨x, hx⟩ := fresh_exists (L ∪ t.fv)
  simp only [Finset.mem_union, not_or] at hx
  rw [subst_intro (x := x) hx.2]
  exact Typing.subst hs (ht x hx.1) hwf

omit [DecidableEq Var] in
/-- Linear substitution of two terms into the body of a tensor elimination. When every finite set of
names misses some name (`[HasFresh Var]`): if `Δ, x : A, y : B ⊢ u.open₂ (fvar x) (fvar y) ∶ C` for
all distinct names `x` and `y` outside a finite set, `Γ₁ ⊢ s₁ ∶ A`, `Γ₂ ⊢ s₂ ∶ B`, and `Γ₁`, `Γ₂`
and `Δ` are pairwise disjoint, then `Γ₁, Γ₂, Δ ⊢ u.open₂ s₁ s₂ ∶ C`. -/
theorem open₂_subst {Γ₂ : Context Var (Ty Base)} {L : Finset Var}
    (hu : ∀ x ∉ L, ∀ y ∉ L, x ≠ y → ⟨y, B⟩ :: ⟨x, A⟩ :: Δ ⊢ u.open₂ (fvar x) (fvar y) ∶ C)
    (hs₁ : Γ₁ ⊢ s₁ ∶ A) (hs₂ : Γ₂ ⊢ s₂ ∶ B) (hwf : (Γ₁ ++ Γ₂ ++ Δ)✓) :
    Γ₁ ++ Γ₂ ++ Δ ⊢ u.open₂ s₁ s₂ ∶ C := by
  classical
  have hslc := hs₁.lc
  obtain ⟨x, hx⟩ := fresh_exists (L ∪ u.fv ∪ (Γ₂ ++ Δ).dom)
  obtain ⟨y, hy⟩ := fresh_exists (insert x (L ∪ u.fv))
  simp only [Finset.mem_insert, Finset.mem_union, not_or] at hx hy
  have hx₂ : x ∉ s₂.fv := fun hm => hx.2 (by
    have := hs₂.fv_subset_dom hm
    simp only [Context.dom, List.keys_append, List.mem_toFinset, List.mem_append] at this ⊢
    exact Or.inl this)
  have hwf' : (Γ₁ ++ (Γ₂ ++ Δ))✓ := by simpa only [List.append_assoc] using hwf
  have hwf₂₃ : (Γ₂ ++ Δ)✓ := List.NodupKeys.sublist (List.sublist_append_right _ _) hwf'
  have h₁ := Typing.subst hs₂ (hu x hx.1.1 y hy.2.1 (Ne.symm hy.1)) (wf_middle hwf₂₃ hx.2)
  have h₂ := Typing.subst hs₁ (h₁.perm List.perm_middle) hwf'
  rw [open₂_eq_subst_rev hx.1.2 hy.2.2 hy.1 hx₂ hslc, List.append_assoc]
  exact h₂

end Typing

end Linear

end LambdaCalculus.LocallyNameless

end Cslib
