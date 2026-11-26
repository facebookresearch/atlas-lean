/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.LocallyNameless.Linear.Typing

/-!
# Tests for linear λ-calculus typing

Statement pins restate every public declaration of
`CSLibExt.Languages.LambdaCalculus.LocallyNameless.Linear.Typing` and are closed by the
declaration itself, so a weakened, strengthened or drifted statement fails here. Each pin sits
in a section with exactly the instance assumptions of its declaration, so an added
`[HasFresh Var]` or `[DecidableEq Var]` also fails. Definitions are pinned by their unfolding
on the constructors that matter: binder shifts, the index convention of `casePair`, and the
fragment predicates.

Concrete checks, with names `ℕ`:

* tensor duplication `λx. ⟨x, x⟩` is rejected at every type, while the additive
  `λx. ⟨|x, x|⟩ : A ⊸ A & A` is accepted;
* `x : A ⊢ ⟨| |⟩ : ⊤` (top discards) but `x : A ⊬ ⟨⟩ : 1` (no weakening);
* the source's rejected `λx. λy. x : A ⊸ B ⊸ A` and accepted
  `λp. case p (⟨x, y⟩ ⇒ ⟨y, x⟩) : A ⊗ B ⊸ B ⊗ A`, which fixes the index convention;
* premise necessity for exactly-once and for usage: a shared additive pair uses its variable
  twice, and `⟨| |⟩` uses none;
* sum elimination with a variable shared by the branches, and a rejected reuse of the
  discriminant's variable in a branch; zero elimination discarding a hypothesis;
* linear substitution with nonempty contexts, and the failure of its conclusion without the
  disjointness premise; the failure of the shared-context substitution property;
* exchange, a cofinite-binder example, and the failure of the usage statements over a finite
  type of names, which is why they assume `[HasFresh Var]`.
-/

@[expose] public section

universe u v

namespace Cslib.LambdaCalculus.LocallyNameless.Linear.TypingTests

open Cslib.LambdaCalculus.LocallyNameless
open Linear Term Ty Context
open scoped Term

/-! ### Statement pins: splitting contexts -/

section SplitPins

variable {α : Type u} {β : Type v} {Γ Γ₁ Γ₂ Δ Δ₁ : Context α β}

/-- Pin: the definition of `Context.Split`. -/
theorem split_def_pin : Γ.Split Γ₁ Γ₂ ↔ Γ✓ ∧ Γ.Perm (Γ₁ ++ Γ₂) := Iff.rfl

/-- Pin: `Context.Split.wf`. -/
theorem split_wf_pin (h : Γ.Split Γ₁ Γ₂) : Γ✓ := h.wf

/-- Pin: `Context.Split.perm`. -/
theorem split_perm_pin (h : Γ.Split Γ₁ Γ₂) : Γ.Perm (Γ₁ ++ Γ₂) := h.perm

/-- Pin: `Context.Split.wf_left`. -/
theorem split_wf_left_pin (h : Γ.Split Γ₁ Γ₂) : Γ₁✓ := h.wf_left

/-- Pin: `Context.Split.wf_right`. -/
theorem split_wf_right_pin (h : Γ.Split Γ₁ Γ₂) : Γ₂✓ := h.wf_right

/-- Pin: `Context.Split.wf_append`. -/
theorem split_wf_append_pin (h : Γ.Split Γ₁ Γ₂) : (Γ₁ ++ Γ₂)✓ := h.wf_append

/-- Pin: `Context.Split.symm`. -/
theorem split_symm_pin (h : Γ.Split Γ₁ Γ₂) : Γ.Split Γ₂ Γ₁ := h.symm

/-- Pin: `Context.Split.perm_whole`. -/
theorem split_perm_whole_pin (h : Γ.Split Γ₁ Γ₂) (hp : Γ.Perm Δ) : Δ.Split Γ₁ Γ₂ :=
  h.perm_whole hp

/-- Pin: `Context.Split.perm_left`. -/
theorem split_perm_left_pin (h : Γ.Split Γ₁ Γ₂) (hp : Γ₁.Perm Δ₁) : Γ.Split Δ₁ Γ₂ :=
  h.perm_left hp

/-- Pin: `Context.split_append_iff`. -/
theorem split_append_iff_pin : (Γ₁ ++ Γ₂).Split Γ₁ Γ₂ ↔ (Γ₁ ++ Γ₂)✓ := split_append_iff

/-- Pin: `Context.split_nil_left_iff`. -/
theorem split_nil_left_iff_pin : Γ.Split [] Δ ↔ Γ✓ ∧ Γ.Perm Δ := split_nil_left_iff

variable [DecidableEq α]

/-- Pin: `Context.Split.disjoint`. -/
theorem split_disjoint_pin (h : Γ.Split Γ₁ Γ₂) : Disjoint Γ₁.dom Γ₂.dom := h.disjoint

/-- Pin: `Context.Split.dom_eq`. -/
theorem split_dom_eq_pin (h : Γ.Split Γ₁ Γ₂) : Γ.dom = Γ₁.dom ∪ Γ₂.dom := h.dom_eq

end SplitPins

/-! ### Statement pins: types, terms and notation -/

section SyntaxPins

variable {Var : Type u} {Base : Type v}

example : Base → Ty Base := Ty.base
example : Ty Base := Ty.one
example : Ty Base → Ty Base → Ty Base := Ty.tensor
example : Ty Base → Ty Base → Ty Base := Ty.lolli
example : Ty Base → Ty Base → Ty Base := Ty.with
example : Ty Base → Ty Base → Ty Base := Ty.oplus
example : Ty Base := Ty.top
example : Ty Base := Ty.zero
example [DecidableEq Base] : DecidableEq (Ty Base) := instDecidableEqTy

/-- Pin: the scoped type notation, with `⊸` right-associative and binding loosest. -/
example (A B C : Ty Base) :
    (A ⊗ B ⊸ B & C ⊸ A ⊕ C) = .lolli (.tensor A B) (.lolli (.with B C) (.oplus A C)) := rfl

example : ℕ → Term Var := Term.bvar
example : Var → Term Var := Term.fvar
example : Term Var → Term Var := Term.abs
example : Term Var → Term Var → Term Var := Term.app
example : Term Var → Term Var → Term Var := Term.pair
example : Term Var → Term Var → Term Var := Term.casePair
example : Term Var := Term.unit
example : Term Var → Term Var → Term Var := Term.caseUnit
example : Term Var → Term Var → Term Var := Term.lpair
example : Term Var → Term Var := Term.proj₁
example : Term Var → Term Var := Term.proj₂
example : Term Var → Term Var := Term.inl
example : Term Var → Term Var := Term.inr
example : Term Var → Term Var → Term Var → Term Var := Term.casePlus
example : Term Var := Term.lunit
example : Term Var → Term Var := Term.caseZero
example [DecidableEq Var] : DecidableEq (Term Var) := instDecidableEqTerm

variable (k i : ℕ) (s s₁ s₂ t u v : Term Var)

/-- Pin: the opening notation is `Term.openRec`. -/
example : t⟦k ↝ s⟧ = Term.openRec k s t := rfl

/-- Pin: `Term.openRec` replaces exactly the index `k`. -/
example : (bvar i : Term Var)⟦k ↝ s⟧ = if k = i then s else bvar i := rfl

/-- Pin: `Term.openRec` shifts by one under `abs`. -/
example : (abs t)⟦k ↝ s⟧ = abs (t⟦k + 1 ↝ s⟧) := rfl

/-- Pin: `Term.openRec` shifts by two under the body of `casePair`. -/
example : (casePair t u)⟦k ↝ s⟧ = casePair (t⟦k ↝ s⟧) (u⟦k + 2 ↝ s⟧) := rfl

/-- Pin: `Term.openRec` shifts by one under each branch of `casePlus`. -/
example : (casePlus t u v)⟦k ↝ s⟧ = casePlus (t⟦k ↝ s⟧) (u⟦k + 1 ↝ s⟧) (v⟦k + 1 ↝ s⟧) := rfl

/-- Pin: `Term.open'` and its notation open the outermost index. -/
example : t ^ s = t⟦0 ↝ s⟧ := rfl

/-- Pin: `Term.open₂` opens index 1 by the first component, then index 0 by the second. -/
example : t.open₂ s₁ s₂ = (t⟦1 ↝ s₁⟧)⟦0 ↝ s₂⟧ := rfl

/-- Pin: the purely multiplicative fragment. -/
example : (abs t).Multiplicative = t.Multiplicative ∧
    (app t u).Multiplicative = (t.Multiplicative ∧ u.Multiplicative) ∧
    (pair t u).Multiplicative = (t.Multiplicative ∧ u.Multiplicative) ∧
    (casePair t u).Multiplicative = (t.Multiplicative ∧ u.Multiplicative) ∧
    (unit : Term Var).Multiplicative ∧
    (caseUnit t u).Multiplicative = (t.Multiplicative ∧ u.Multiplicative) ∧
    ¬ (lpair t u).Multiplicative ∧ ¬ (proj₁ t).Multiplicative ∧ ¬ (proj₂ t).Multiplicative ∧
    ¬ (inl t).Multiplicative ∧ ¬ (inr t).Multiplicative ∧
    ¬ (casePlus t u v).Multiplicative ∧ ¬ (lunit : Term Var).Multiplicative ∧
    ¬ (caseZero t).Multiplicative :=
  ⟨rfl, rfl, rfl, rfl, trivial, rfl, id, id, id, id, id, id, id, id⟩

/-- Pin: only `lunit` and `caseZero` discard. -/
example : ¬ (lunit : Term Var).NoDiscard ∧ ¬ (caseZero t).NoDiscard ∧
    (casePlus t u v).NoDiscard = (t.NoDiscard ∧ u.NoDiscard ∧ v.NoDiscard) ∧
    (lpair t u).NoDiscard = (t.NoDiscard ∧ u.NoDiscard) ∧ (unit : Term Var).NoDiscard :=
  ⟨id, id, rfl, rfl, trivial⟩

/-- Pin: the local-closure rules for the binders. -/
example (L : Finset Var) (ht : t.LC)
    (hu : ∀ x ∉ L, ∀ y ∉ L, x ≠ y → (u.open₂ (fvar x) (fvar y)).LC) : (casePair t u).LC :=
  LC.casePair L ht hu

example (L : Finset Var) (ht : ∀ x ∉ L, (t ^ fvar x).LC) : (abs t).LC := LC.abs L ht

example (L : Finset Var) (ht : t.LC) (hu : ∀ x ∉ L, (u ^ fvar x).LC)
    (hv : ∀ y ∉ L, (v ^ fvar y).LC) : (casePlus t u v).LC :=
  LC.casePlus L ht hu hv

example (x : Var) : (fvar x : Term Var).LC := LC.fvar x
example (ht : t.LC) (hu : u.LC) : (app t u).LC := LC.app ht hu
example (ht : t.LC) (hu : u.LC) : (pair t u).LC := LC.pair ht hu
example : (unit : Term Var).LC := LC.unit
example (ht : t.LC) (hu : u.LC) : (caseUnit t u).LC := LC.caseUnit ht hu
example (ht : t.LC) (hu : u.LC) : (lpair t u).LC := LC.lpair ht hu
example (ht : t.LC) : (proj₁ t).LC := LC.proj₁ ht
example (ht : t.LC) : (proj₂ t).LC := LC.proj₂ ht
example (ht : t.LC) : (inl t).LC := LC.inl ht
example (ht : t.LC) : (inr t).LC := LC.inr ht
example : (lunit : Term Var).LC := LC.lunit
example (ht : t.LC) : (caseZero t).LC := LC.caseZero ht

variable [DecidableEq Var] (x y : Var)

/-- Pin: free variables, counted with multiplicity by `Term.occ`. -/
example : (casePlus t u v).fv = t.fv ∪ u.fv ∪ v.fv ∧ (casePair t u).fv = t.fv ∪ u.fv ∧
    (fvar y : Term Var).fv = {y} ∧ (bvar i : Term Var).fv = ∅ :=
  ⟨rfl, rfl, rfl, rfl⟩

example : (fvar y : Term Var).occ x = (if x = y then 1 else 0) ∧
    (lpair t u).occ x = t.occ x + u.occ x ∧
    (casePlus t u v).occ x = t.occ x + u.occ x + v.occ x ∧ (lunit : Term Var).occ x = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Pin: the substitution instance and its notation. -/
example : t[x := s] = t.subst x s := rfl

example : (instHasSubstitutionTerm : HasSubstitution (Term Var) Var (Term Var)).subst t x s =
    t.subst x s := rfl

example : (fvar y : Term Var)[x := s] = (if x = y then s else fvar y) ∧
    (casePair t u)[x := s] = casePair (t[x := s]) (u[x := s]) ∧
    (bvar i : Term Var)[x := s] = bvar i :=
  ⟨rfl, rfl, rfl⟩

end SyntaxPins

/-! ### Statement pins: laws of the locally nameless operations -/

section TermLawPins

variable {Var : Type u} {t u v s s₁ s₂ : Term Var} {x y : Var}

section
variable [DecidableEq Var]

/-- Pin: `Term.occ_eq_zero_iff`. -/
theorem occ_eq_zero_iff_pin : t.occ x = 0 ↔ x ∉ t.fv := occ_eq_zero_iff

/-- Pin: `Term.subst_fresh`. -/
theorem subst_fresh_pin (h : x ∉ t.fv) : t[x := s] = t := subst_fresh h

/-- Pin: `Term.subst_intro`. -/
theorem subst_intro_pin (h : x ∉ t.fv) : t ^ s = (t ^ fvar x)[x := s] := subst_intro h

end

variable [HasFresh Var]

/-- Pin: `Term.open_lc`. -/
theorem open_lc_pin (k : ℕ) (s : Term Var) (h : t.LC) : t⟦k ↝ s⟧ = t := open_lc k s h

/-- Pin: `Term.beta_lc`. -/
theorem beta_lc_pin (h : (abs t).LC) (hs : s.LC) : (t ^ s).LC := beta_lc h hs

/-- Pin: `Term.casePair_lc_open₂`. -/
theorem casePair_lc_open₂_pin (h : (casePair t u).LC) (hs₁ : s₁.LC) (hs₂ : s₂.LC) :
    (u.open₂ s₁ s₂).LC :=
  casePair_lc_open₂ h hs₁ hs₂

/-- Pin: `Term.casePlus_lc_open_left`. -/
theorem casePlus_lc_open_left_pin (h : (casePlus t u v).LC) (hs : s.LC) : (u ^ s).LC :=
  casePlus_lc_open_left h hs

/-- Pin: `Term.casePlus_lc_open_right`. -/
theorem casePlus_lc_open_right_pin (h : (casePlus t u v).LC) (hs : s.LC) : (v ^ s).LC :=
  casePlus_lc_open_right h hs

variable [DecidableEq Var]

/-- Pin: `Term.subst_open`. -/
theorem subst_open_pin (hs : s.LC) : (t ^ u)[x := s] = t[x := s] ^ u[x := s] := subst_open hs

/-- Pin: `Term.subst_open_var`. -/
theorem subst_open_var_pin (hxy : y ≠ x) (hs : s.LC) :
    (t ^ fvar y)[x := s] = t[x := s] ^ fvar y :=
  subst_open_var hxy hs

/-- Pin: `Term.subst_lc`. -/
theorem subst_lc_pin (ht : t.LC) (hs : s.LC) : (t[x := s]).LC := subst_lc ht hs

end TermLawPins

/-! ### Statement pins: the typing rules -/

section RulePins

variable {Var : Type u} {Base : Type v} {Γ Γ₁ Γ₂ Δ : Context Var (Ty Base)}
  {t u v s : Term Var} {A B C : Ty Base} (L : Finset Var)

/-- Pin: the judgment notation. -/
example : (Γ ⊢ t ∶ A) = Typing Γ t A := rfl

example (x : Var) : [⟨x, A⟩] ⊢ fvar x ∶ A := Typing.var

example (h : ∀ x ∉ L, ⟨x, A⟩ :: Γ ⊢ t ^ fvar x ∶ B) : Γ ⊢ .abs t ∶ (.lolli A B) :=
  Typing.abs L h

example (h : Γ.Split Γ₁ Γ₂) (ht : Γ₁ ⊢ t ∶ (.lolli A B)) (hs : Γ₂ ⊢ s ∶ A) :
    Γ ⊢ .app t s ∶ B :=
  Typing.app h ht hs

example (h : Γ.Split Γ₁ Γ₂) (ht : Γ₁ ⊢ t ∶ A) (hs : Γ₂ ⊢ s ∶ B) :
    Γ ⊢ .pair t s ∶ (.tensor A B) :=
  Typing.pair h ht hs

example (h : Γ.Split Γ₁ Δ) (ht : Γ₁ ⊢ t ∶ (.tensor A B))
    (hu : ∀ x ∉ L, ∀ y ∉ L, x ≠ y → ⟨y, B⟩ :: ⟨x, A⟩ :: Δ ⊢ u.open₂ (fvar x) (fvar y) ∶ C) :
    Γ ⊢ .casePair t u ∶ C :=
  Typing.casePair L h ht hu

example : ([] : Context Var (Ty Base)) ⊢ .unit ∶ .one := Typing.unit

example (h : Γ.Split Γ₁ Δ) (ht : Γ₁ ⊢ t ∶ .one) (hu : Δ ⊢ u ∶ C) : Γ ⊢ .caseUnit t u ∶ C :=
  Typing.caseUnit h ht hu

example (ht : Γ ⊢ t ∶ A) (hs : Γ ⊢ s ∶ B) : Γ ⊢ .lpair t s ∶ (.with A B) :=
  Typing.lpair ht hs

example (ht : Γ ⊢ t ∶ (.with A B)) : Γ ⊢ .proj₁ t ∶ A := Typing.proj₁ ht

example (ht : Γ ⊢ t ∶ (.with A B)) : Γ ⊢ .proj₂ t ∶ B := Typing.proj₂ ht

example (ht : Γ ⊢ t ∶ A) : Γ ⊢ .inl t ∶ (.oplus A B) := Typing.inl ht

example (ht : Γ ⊢ t ∶ B) : Γ ⊢ .inr t ∶ (.oplus A B) := Typing.inr ht

example (h : Γ.Split Γ₁ Δ) (ht : Γ₁ ⊢ t ∶ (.oplus A B))
    (hu : ∀ x ∉ L, ⟨x, A⟩ :: Δ ⊢ u ^ fvar x ∶ C) (hv : ∀ y ∉ L, ⟨y, B⟩ :: Δ ⊢ v ^ fvar y ∶ C) :
    Γ ⊢ .casePlus t u v ∶ C :=
  Typing.casePlus L h ht hu hv

example (h : Γ✓) : Γ ⊢ .lunit ∶ .top := Typing.lunit h

example (h : Γ.Split Γ₁ Δ) (ht : Γ₁ ⊢ t ∶ .zero) : Γ ⊢ .caseZero t ∶ C := Typing.caseZero h ht

end RulePins

/-! ### Statement pins: typing theorems -/

section TypingPins

variable {Var : Type u} {Base : Type v} {Γ Γ₁ Γ₂ Δ : Context Var (Ty Base)}
  {t u v s s₁ s₂ : Term Var} {A B C : Ty Base} {x : Var}

/-- Pin: `Typing.perm`. -/
theorem perm_pin (h : Γ ⊢ t ∶ A) (hp : Γ.Perm Δ) : Δ ⊢ t ∶ A := h.perm hp

/-- Pin: `Typing.lc`. -/
theorem lc_pin (h : Γ ⊢ t ∶ A) : t.LC := h.lc

/-- Pin: `Typing.var_iff`. -/
theorem var_iff_pin : Γ ⊢ fvar x ∶ A ↔ Γ = [⟨x, A⟩] := Typing.var_iff

/-- Pin: `Typing.unit_iff`. -/
theorem unit_iff_pin : Γ ⊢ .unit ∶ A ↔ Γ = [] ∧ A = .one := Typing.unit_iff

/-- Pin: `Typing.abs_iff`. -/
theorem abs_iff_pin : Γ ⊢ .abs t ∶ C ↔
    ∃ A B, C = .lolli A B ∧ ∃ L : Finset Var, ∀ x ∉ L, ⟨x, A⟩ :: Γ ⊢ t ^ fvar x ∶ B :=
  Typing.abs_iff

/-- Pin: `Typing.app_iff`. -/
theorem app_iff_pin : Γ ⊢ .app t s ∶ B ↔
    ∃ A Γ₁ Γ₂, Γ.Split Γ₁ Γ₂ ∧ Γ₁ ⊢ t ∶ (.lolli A B) ∧ Γ₂ ⊢ s ∶ A :=
  Typing.app_iff

/-- Pin: `Typing.pair_iff`. -/
theorem pair_iff_pin : Γ ⊢ .pair t s ∶ C ↔
    ∃ A B Γ₁ Γ₂, C = .tensor A B ∧ Γ.Split Γ₁ Γ₂ ∧ Γ₁ ⊢ t ∶ A ∧ Γ₂ ⊢ s ∶ B :=
  Typing.pair_iff

/-- Pin: `Typing.casePair_iff`. -/
theorem casePair_iff_pin : Γ ⊢ .casePair t u ∶ C ↔
    ∃ A B Γ₁ Δ, Γ.Split Γ₁ Δ ∧ Γ₁ ⊢ t ∶ (.tensor A B) ∧ ∃ L : Finset Var,
      ∀ x ∉ L, ∀ y ∉ L, x ≠ y → ⟨y, B⟩ :: ⟨x, A⟩ :: Δ ⊢ u.open₂ (fvar x) (fvar y) ∶ C :=
  Typing.casePair_iff

/-- Pin: `Typing.caseUnit_iff`. -/
theorem caseUnit_iff_pin : Γ ⊢ .caseUnit t u ∶ C ↔
    ∃ Γ₁ Δ, Γ.Split Γ₁ Δ ∧ Γ₁ ⊢ t ∶ .one ∧ Δ ⊢ u ∶ C :=
  Typing.caseUnit_iff

/-- Pin: `Typing.lpair_iff`. -/
theorem lpair_iff_pin : Γ ⊢ .lpair t s ∶ C ↔ ∃ A B, C = .with A B ∧ Γ ⊢ t ∶ A ∧ Γ ⊢ s ∶ B :=
  Typing.lpair_iff

/-- Pin: `Typing.proj₁_iff`. -/
theorem proj₁_iff_pin : Γ ⊢ .proj₁ t ∶ A ↔ ∃ B, Γ ⊢ t ∶ (.with A B) := Typing.proj₁_iff

/-- Pin: `Typing.proj₂_iff`. -/
theorem proj₂_iff_pin : Γ ⊢ .proj₂ t ∶ B ↔ ∃ A, Γ ⊢ t ∶ (.with A B) := Typing.proj₂_iff

/-- Pin: `Typing.inl_iff`. -/
theorem inl_iff_pin : Γ ⊢ .inl t ∶ C ↔ ∃ A B, C = .oplus A B ∧ Γ ⊢ t ∶ A := Typing.inl_iff

/-- Pin: `Typing.inr_iff`. -/
theorem inr_iff_pin : Γ ⊢ .inr t ∶ C ↔ ∃ A B, C = .oplus A B ∧ Γ ⊢ t ∶ B := Typing.inr_iff

/-- Pin: `Typing.casePlus_iff`. -/
theorem casePlus_iff_pin : Γ ⊢ .casePlus t u v ∶ C ↔
    ∃ A B Γ₁ Δ, Γ.Split Γ₁ Δ ∧ Γ₁ ⊢ t ∶ (.oplus A B) ∧ ∃ L : Finset Var,
      (∀ x ∉ L, ⟨x, A⟩ :: Δ ⊢ u ^ fvar x ∶ C) ∧ (∀ y ∉ L, ⟨y, B⟩ :: Δ ⊢ v ^ fvar y ∶ C) :=
  Typing.casePlus_iff

/-- Pin: `Typing.lunit_iff`. -/
theorem lunit_iff_pin : Γ ⊢ .lunit ∶ A ↔ A = .top ∧ Γ✓ := Typing.lunit_iff

/-- Pin: `Typing.caseZero_iff`. -/
theorem caseZero_iff_pin : Γ ⊢ .caseZero t ∶ C ↔ ∃ Γ₁ Δ, Γ.Split Γ₁ Δ ∧ Γ₁ ⊢ t ∶ .zero :=
  Typing.caseZero_iff

variable [HasFresh Var]

/-- Pin: `Typing.wf`. -/
theorem wf_pin (h : Γ ⊢ t ∶ A) : Γ✓ := h.wf

/-- Pin: `Typing.open_subst`. -/
theorem open_subst_pin {L : Finset Var} (ht : ∀ x ∉ L, ⟨x, A⟩ :: Δ ⊢ t ^ fvar x ∶ B)
    (hs : Γ ⊢ s ∶ A) (hwf : (Γ ++ Δ)✓) : Γ ++ Δ ⊢ t ^ s ∶ B :=
  Typing.open_subst ht hs hwf

/-- Pin: `Typing.open₂_subst`. -/
theorem open₂_subst_pin {L : Finset Var}
    (hu : ∀ x ∉ L, ∀ y ∉ L, x ≠ y → ⟨y, B⟩ :: ⟨x, A⟩ :: Δ ⊢ u.open₂ (fvar x) (fvar y) ∶ C)
    (hs₁ : Γ₁ ⊢ s₁ ∶ A) (hs₂ : Γ₂ ⊢ s₂ ∶ B) (hwf : (Γ₁ ++ Γ₂ ++ Δ)✓) :
    Γ₁ ++ Γ₂ ++ Δ ⊢ u.open₂ s₁ s₂ ∶ C :=
  Typing.open₂_subst hu hs₁ hs₂ hwf

variable [DecidableEq Var]

/-- Pin: `Typing.fv_subset_dom`. -/
theorem fv_subset_dom_pin (h : Γ ⊢ t ∶ A) : t.fv ⊆ Γ.dom := h.fv_subset_dom

/-- Pin: `Typing.dom_subset_fv`. -/
theorem dom_subset_fv_pin (h : Γ ⊢ t ∶ A) (ht : t.NoDiscard) : Γ.dom ⊆ t.fv :=
  h.dom_subset_fv ht

/-- Pin: `Typing.app_fv_disjoint`. -/
theorem app_fv_disjoint_pin (h : Γ ⊢ .app t s ∶ B) : Disjoint t.fv s.fv := h.app_fv_disjoint

/-- Pin: `Typing.pair_fv_disjoint`. -/
theorem pair_fv_disjoint_pin (h : Γ ⊢ .pair t s ∶ C) : Disjoint t.fv s.fv :=
  h.pair_fv_disjoint

/-- Pin: `Typing.casePair_fv_disjoint`. -/
theorem casePair_fv_disjoint_pin (h : Γ ⊢ .casePair t u ∶ C) : Disjoint t.fv u.fv :=
  h.casePair_fv_disjoint

/-- Pin: `Typing.caseUnit_fv_disjoint`. -/
theorem caseUnit_fv_disjoint_pin (h : Γ ⊢ .caseUnit t u ∶ C) : Disjoint t.fv u.fv :=
  h.caseUnit_fv_disjoint

/-- Pin: `Typing.casePlus_fv_disjoint`. -/
theorem casePlus_fv_disjoint_pin (h : Γ ⊢ .casePlus t u v ∶ C) :
    Disjoint t.fv (u.fv ∪ v.fv) :=
  h.casePlus_fv_disjoint

/-- Pin: `Typing.lpair_fv_eq`. -/
theorem lpair_fv_eq_pin (h : Γ ⊢ .lpair t s ∶ C) (ht : t.NoDiscard) (hs : s.NoDiscard) :
    t.fv = s.fv :=
  h.lpair_fv_eq ht hs

/-- Pin: `Typing.casePlus_fv_eq`. -/
theorem casePlus_fv_eq_pin (h : Γ ⊢ .casePlus t u v ∶ C) (hu : u.NoDiscard)
    (hv : v.NoDiscard) : u.fv = v.fv :=
  h.casePlus_fv_eq hu hv

/-- Pin: `Typing.occ_eq_one`. -/
theorem occ_eq_one_pin (h : Γ ⊢ t ∶ A) (ht : t.Multiplicative) (hx : x ∈ Γ.dom) :
    t.occ x = 1 :=
  h.occ_eq_one ht hx

/-- Pin: `Typing.occ_eq_zero`. -/
theorem occ_eq_zero_pin (h : Γ ⊢ t ∶ A) (hx : x ∉ Γ.dom) : t.occ x = 0 := h.occ_eq_zero hx

/-- Pin: `Typing.subst`, Property 1 of the notes. -/
theorem subst_pin (hs : Γ ⊢ s ∶ A) (ht : ⟨x, A⟩ :: Δ ⊢ t ∶ B) (hwf : (Γ ++ Δ)✓) :
    Γ ++ Δ ⊢ t[x := s] ∶ B :=
  Typing.subst hs ht hwf

end TypingPins

/-! ### Boundary tests -/

section Boundary

variable {Base : Type v} (A B C : Ty Base)

/-- Tensor duplication `λx. ⟨x, x⟩` is rejected at every type. -/
theorem tensor_dup_rejected (T : Ty Base) :
    ¬ ([] : Context ℕ (Ty Base)) ⊢ .abs (.pair (.bvar 0) (.bvar 0)) ∶ T := by
  intro h
  obtain ⟨A', B', -, L, hL⟩ := Typing.abs_iff.1 h
  obtain ⟨x, hx⟩ := fresh_exists L
  have := (hL x hx).pair_fv_disjoint
  simp [Term.openRec, Term.fv] at this

/-- The additive pair shares: `λx. ⟨|x, x|⟩ : A ⊸ A & A`. -/
theorem with_dup_accepted :
    ([] : Context ℕ (Ty Base)) ⊢ .abs (.lpair (.bvar 0) (.bvar 0)) ∶ (A ⊸ A & A) :=
  Typing.abs ∅ fun _ _ => Typing.lpair Typing.var Typing.var

/-- `⊤` discards: `x : A ⊢ ⟨| |⟩ : ⊤`. -/
theorem top_discards : ([⟨0, A⟩] : Context ℕ (Ty Base)) ⊢ .lunit ∶ .top :=
  Typing.lunit (List.nodupKeys_singleton _)

/-- The multiplicative unit does not discard: `x : A ⊬ ⟨⟩ : 1`, so weakening fails. -/
theorem one_needs_empty : ¬ ([⟨0, A⟩] : Context ℕ (Ty Base)) ⊢ .unit ∶ .one := by
  intro h
  exact absurd (Typing.unit_iff.1 h).1 (by simp)

/-- The source's rejected term `λx. λy. x : A ⊸ B ⊸ A` (an extraneous hypothesis). -/
theorem const_rejected :
    ¬ ([] : Context ℕ (Ty Base)) ⊢ .abs (.abs (.bvar 1)) ∶ (A ⊸ B ⊸ A) := by
  intro h
  obtain ⟨A', B', -, L, hL⟩ := Typing.abs_iff.1 h
  obtain ⟨x, hx⟩ := fresh_exists L
  obtain ⟨A'', B'', -, L', hL'⟩ := Typing.abs_iff.1 (hL x hx)
  obtain ⟨y, hy⟩ := fresh_exists L'
  have := Typing.var_iff.1 (hL' y hy)
  simp at this

/-- The source's accepted swap `λp. case p (⟨x, y⟩ ⇒ ⟨y, x⟩) : A ⊗ B ⊸ B ⊗ A`; in the body
`bvar 1` is `x` and `bvar 0` is `y`. -/
theorem swap_accepted :
    ([] : Context ℕ (Ty Base)) ⊢ .abs (.casePair (.bvar 0) (.pair (.bvar 0) (.bvar 1))) ∶
      (A ⊗ B ⊸ B ⊗ A) :=
  Typing.abs ∅ fun p _ =>
    Typing.casePair (Γ₁ := [⟨p, A ⊗ B⟩]) (Δ := []) ∅ ⟨List.nodupKeys_singleton _, by simp⟩
      Typing.var fun x _ y _ hxy => Typing.pair (Γ₁ := [⟨y, B⟩]) (Γ₂ := [⟨x, A⟩])
        ⟨by show List.NodupKeys _; simp [List.NodupKeys, List.keys, Ne.symm hxy],
          List.Perm.refl _⟩ Typing.var Typing.var

/-- With the indices exchanged the same shape is the identity on pairs. -/
theorem pair_id_accepted :
    ([] : Context ℕ (Ty Base)) ⊢ .abs (.casePair (.bvar 0) (.pair (.bvar 1) (.bvar 0))) ∶
      (A ⊗ B ⊸ A ⊗ B) :=
  Typing.abs ∅ fun p _ =>
    Typing.casePair (Γ₁ := [⟨p, A ⊗ B⟩]) (Δ := []) ∅ ⟨List.nodupKeys_singleton _, by simp⟩
      Typing.var fun x _ y _ hxy => Typing.pair (Γ₁ := [⟨x, A⟩]) (Γ₂ := [⟨y, B⟩])
        ⟨by show List.NodupKeys _; simp [List.NodupKeys, List.keys, Ne.symm hxy],
          List.Perm.swap _ _ _⟩ Typing.var Typing.var

/-- The index convention of `casePair` on the body of the swap. -/
example : (Term.pair (.bvar 0) (.bvar 1) : Term ℕ).open₂ (.fvar 1) (.fvar 2) =
    .pair (.fvar 2) (.fvar 1) := rfl

/-- Opening under `abs` does not reach the body of `casePair` at index 0. -/
example : (Term.casePair (.bvar 0) (.pair (.bvar 0) (.bvar 1)) : Term ℕ).open' (.fvar 5) =
    .casePair (.fvar 5) (.pair (.bvar 0) (.bvar 1)) := rfl

/-- Exactly-once needs the multiplicative fragment: a shared additive pair is typed and uses
its variable twice. -/
theorem with_pair_typed :
    ([⟨0, A⟩] : Context ℕ (Ty Base)) ⊢ .lpair (.fvar 0) (.fvar 0) ∶ (A & A) :=
  Typing.lpair Typing.var Typing.var

example : (Term.lpair (.fvar 0) (.fvar 0) : Term ℕ).occ 0 = 2 ∧
    ¬ (Term.lpair (.fvar 0) (.fvar 0) : Term ℕ).Multiplicative :=
  ⟨rfl, id⟩

/-- The usage lemmas need their premises: `⟨| |⟩` is typed in `x : A` and uses no variable. -/
example : (Term.lunit : Term ℕ).occ 0 = 0 ∧ (Term.lunit : Term ℕ).fv = ∅ ∧
    ¬ (Term.lunit : Term ℕ).NoDiscard ∧ ¬ (Term.lunit : Term ℕ).Multiplicative :=
  ⟨rfl, rfl, id, id⟩

/-- Sum elimination: both branches use the shared `w`. -/
theorem casePlus_shared_accepted :
    ([⟨0, A ⊕ A⟩, ⟨1, B⟩] : Context ℕ (Ty Base)) ⊢
      .casePlus (.fvar 0) (.pair (.bvar 0) (.fvar 1)) (.pair (.bvar 0) (.fvar 1)) ∶ (A ⊗ B) :=
    Typing.casePlus (Γ₁ := [⟨0, A ⊕ A⟩]) (Δ := [⟨1, B⟩]) {1}
      ⟨by show List.NodupKeys _; simp [List.NodupKeys, List.keys], List.Perm.refl _⟩ Typing.var
      (fun x hx => Typing.pair (Γ₁ := [⟨x, A⟩]) (Γ₂ := [⟨1, B⟩])
        ⟨by show List.NodupKeys _; simp_all [List.NodupKeys, List.keys],
          List.Perm.refl _⟩ Typing.var Typing.var)
      (fun y hy => Typing.pair (Γ₁ := [⟨y, A⟩]) (Γ₂ := [⟨1, B⟩])
        ⟨by show List.NodupKeys _; simp_all [List.NodupKeys, List.keys],
          List.Perm.refl _⟩ Typing.var Typing.var)

/-- Sum elimination: the discriminant's variable cannot be reused in a branch. -/
theorem casePlus_reuse_rejected (T : Ty Base) :
    ¬ ([⟨0, A ⊕ A⟩] : Context ℕ (Ty Base)) ⊢
      .casePlus (.fvar 0) (.pair (.bvar 0) (.fvar 0)) (.pair (.bvar 0) (.fvar 0)) ∶ T := by
  intro h
  have := h.casePlus_fv_disjoint
  simp [Term.fv] at this

/-- Zero elimination discards the other hypotheses. -/
theorem caseZero_discards :
    ([⟨0, .zero⟩, ⟨1, A⟩] : Context ℕ (Ty Base)) ⊢ .caseZero (.fvar 0) ∶ C :=
  Typing.caseZero (Γ₁ := [⟨0, .zero⟩]) (Δ := [⟨1, A⟩])
    ⟨by show List.NodupKeys _; simp [List.NodupKeys, List.keys], List.Perm.refl _⟩ Typing.var

/-- Linear substitution with nonempty contexts: `x : A ⊢ x : A` and `z : A, y : B ⊢ ⟨z, y⟩`
give `x : A, y : B ⊢ ⟨x, y⟩ : A ⊗ B`. -/
theorem subst_nonempty :
    ([⟨0, A⟩] ++ [⟨1, B⟩] : Context ℕ (Ty Base)) ⊢
      (Term.pair (.fvar 2) (.fvar 1))[2 := Term.fvar 0] ∶ (A ⊗ B) :=
  Typing.subst Typing.var
    (Typing.pair (Γ₁ := [⟨2, A⟩]) (Γ₂ := [⟨1, B⟩])
      ⟨by show List.NodupKeys _; simp [List.NodupKeys, List.keys],
        List.Perm.refl _⟩ Typing.var Typing.var)
    (by show List.NodupKeys _; simp [List.NodupKeys, List.keys])

example : (Term.pair (.fvar 2) (.fvar 1) : Term ℕ)[2 := Term.fvar 0] = .pair (.fvar 0) (.fvar 1) :=
  rfl

/-- Linear substitution needs disjoint contexts: both premises hold for `Γ = Δ = y : A`, and
the conclusion fails. -/
theorem subst_needs_disjoint :
    ([⟨0, A⟩] : Context ℕ (Ty Base)) ⊢ .fvar 0 ∶ A ∧
      ([⟨1, A⟩, ⟨0, A⟩] : Context ℕ (Ty Base)) ⊢ .pair (.fvar 1) (.fvar 0) ∶ (A ⊗ A) ∧
      ¬ ([⟨0, A⟩] ++ [⟨0, A⟩] : Context ℕ (Ty Base)) ⊢
        (Term.pair (.fvar 1) (.fvar 0))[1 := Term.fvar 0] ∶ (A ⊗ A) :=
  ⟨Typing.var,
    Typing.pair (Γ₁ := [⟨1, A⟩]) (Γ₂ := [⟨0, A⟩])
      ⟨by show List.NodupKeys _; simp [List.NodupKeys, List.keys],
        List.Perm.refl _⟩ Typing.var Typing.var,
    fun h => by
      have := h.wf
      simp [HasWellFormed.wf, List.NodupKeys, List.keys] at this⟩

/-- The shared-context substitution property of structural type systems fails for linear
typing: with `Γ = y : A`, `x : A, y : A ⊢ ⟨x, y⟩ : A ⊗ A` and `Γ ⊢ y : A`, but
`Γ ⊬ ⟨y, y⟩ : A ⊗ A`. -/
theorem shared_subst_fails :
    ¬ ∀ (Γ : Context ℕ (Ty Base)) (x : ℕ) (A B : Ty Base) (t s : Term ℕ),
      ⟨x, A⟩ :: Γ ⊢ t ∶ B → Γ ⊢ s ∶ A → Γ ⊢ t[x := s] ∶ B := by
  intro H
  have h := H [⟨0, .one⟩] 1 .one (.tensor .one .one) (.pair (.fvar 1) (.fvar 0)) (.fvar 0)
    (Typing.pair (Γ₁ := [⟨1, .one⟩]) (Γ₂ := [⟨0, .one⟩])
      ⟨by show List.NodupKeys _; simp [List.NodupKeys, List.keys],
        List.Perm.refl _⟩ Typing.var Typing.var)
    Typing.var
  have h' : ([⟨0, .one⟩] : Context ℕ (Ty Base)) ⊢ .pair (.fvar 0) (.fvar 0) ∶ (.tensor .one .one) :=
    h
  have := h'.pair_fv_disjoint
  simp [Term.fv] at this

/-- Exchange: a context and its permutation type the same pair. -/
theorem exchange_example :
    ([⟨0, A⟩, ⟨1, B⟩] : Context ℕ (Ty Base)) ⊢ .pair (.fvar 0) (.fvar 1) ∶ (A ⊗ B) ∧
      ([⟨1, B⟩, ⟨0, A⟩] : Context ℕ (Ty Base)) ⊢ .pair (.fvar 0) (.fvar 1) ∶ (A ⊗ B) :=
  ⟨Typing.pair (Γ₁ := [⟨0, A⟩]) (Γ₂ := [⟨1, B⟩])
      ⟨by show List.NodupKeys _; simp [List.NodupKeys, List.keys], List.Perm.refl _⟩
      Typing.var Typing.var,
    Typing.pair (Γ₁ := [⟨0, A⟩]) (Γ₂ := [⟨1, B⟩])
      ⟨by show List.NodupKeys _; simp [List.NodupKeys, List.keys], List.Perm.swap _ _ _⟩
      Typing.var Typing.var⟩

/-- A cofinite binder: linear application under two abstractions. -/
theorem apply_accepted :
    ([] : Context ℕ (Ty Base)) ⊢ .abs (.abs (.app (.bvar 1) (.bvar 0))) ∶ ((A ⊸ B) ⊸ A ⊸ B) :=
    Typing.abs ∅ fun f _ => Typing.abs {f} fun x hx =>
      Typing.app (Γ₁ := [⟨f, A ⊸ B⟩]) (Γ₂ := [⟨x, A⟩])
        ⟨by show List.NodupKeys _; simp_all [List.NodupKeys, List.keys],
          List.Perm.swap _ _ _⟩ Typing.var Typing.var

/-- Over a finite type of names the cofinite premise of `abs` can be empty: with names `Unit`,
`⊢ λ_. x : A ⊸ A` holds although `x` is not a hypothesis, so `Typing.fv_subset_dom`,
`Typing.dom_subset_fv` and `Typing.occ_eq_one` need `[HasFresh Var]`. -/
theorem finite_names_vacuous :
    ([] : Context Unit (Ty Base)) ⊢ .abs (.fvar ()) ∶ (A ⊸ A) ∧
      ([⟨(), A⟩] : Context Unit (Ty Base)) ⊢ .abs (.bvar 0) ∶ (B ⊸ B) ∧
      ¬ (Term.abs (.fvar ()) : Term Unit).fv ⊆ Context.dom ([] : Context Unit (Ty Base)) ∧
      (Term.abs (.bvar 0) : Term Unit).occ () = 0 :=
  ⟨Typing.abs {()} fun x hx => absurd (by cases x; exact Finset.mem_singleton_self ()) hx,
    Typing.abs {()} fun x hx => absurd (by cases x; exact Finset.mem_singleton_self ()) hx,
    by simp [Term.fv, Context.dom], rfl⟩

end Boundary

end Cslib.LambdaCalculus.LocallyNameless.Linear.TypingTests
