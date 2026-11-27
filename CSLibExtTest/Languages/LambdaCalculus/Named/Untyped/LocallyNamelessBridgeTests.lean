/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.Named.Untyped.LocallyNamelessBridge

/-!
# Tests for the translation of named terms into locally nameless terms

The defining equations of `toLocallyNameless`; concrete translations over `Var := ℕ` (binders,
index shifts, shadowing, applications, and the examples of Charguéraud's Sections 2.3 and 2.4);
uses of the three clauses of the bijection; two controls (a translation that does not close
binders, and names over `Unit`, where injectivity and surjectivity fail); and the signature of
every public declaration.
-/

namespace Cslib.LambdaCalculus.Named.Untyped.LocallyNamelessBridgeTests

open LocallyNamelessBridge
open LocallyNameless.Untyped.Term (fvar LcAt)
open scoped LocallyNameless.Untyped.Term

universe u

/-! ### The defining equations, for every type of names -/

example {Var : Type u} [DecidableEq Var] (x : Var) :
    toLocallyNameless (.var x : Term Var) = .fvar x := rfl

example {Var : Type u} [DecidableEq Var] (x : Var) (m : Term Var) :
    toLocallyNameless (.abs x m) = .abs ((toLocallyNameless m)⟦0 ↜ x⟧) := rfl

example {Var : Type u} [DecidableEq Var] (m n : Term Var) :
    toLocallyNameless (.app m n) = .app (toLocallyNameless m) (toLocallyNameless n) := rfl

/-! ### Concrete translations over `ℕ` -/

/-- T-a: `λ0.0` becomes `abs (bvar 0)`. -/
example : toLocallyNameless (.abs 0 (.var 0) : Term ℕ) = .abs (.bvar 0) := rfl

/-- T-b: an index counts the binders in between: `λ0.λ1.0` becomes `abs (abs (bvar 1))`. -/
example : toLocallyNameless (.abs 0 (.abs 1 (.var 0)) : Term ℕ) = .abs (.abs (.bvar 1)) := rfl

/-- T-c: the inner binder shadows the outer one: `λ0.λ0.0` becomes `abs (abs (bvar 0))`. -/
example : toLocallyNameless (.abs 0 (.abs 0 (.var 0)) : Term ℕ) = .abs (.abs (.bvar 0)) := rfl

/-- Charguéraud, Section 2.4, with `x := 0` and `y := 1`: `λx. x y` becomes
`abs (app (bvar 0) (fvar y))`. -/
example : toLocallyNameless (.abs 0 (.app (.var 0) (.var 1)) : Term ℕ) =
    .abs (.app (.bvar 0) (.fvar 1)) := rfl

/-- Charguéraud, Section 2.3, with `x := 0` and `y := 1`: `λx. (λy. y x) x` becomes
`abs (app (abs (app (bvar 0) (bvar 1))) (bvar 0))`. -/
example : toLocallyNameless (.abs 0 (.app (.abs 1 (.app (.var 1) (.var 0))) (.var 0)) : Term ℕ) =
    .abs (.app (.abs (.app (.bvar 0) (.bvar 1))) (.bvar 0)) := rfl

/-! ### The three clauses at work -/

/-- T-d: `λ0.0` and `λ1.1` have the same translation, so by clause 2 they are α-equivalent. -/
example : toLocallyNameless (.abs 0 (.var 0) : Term ℕ) = toLocallyNameless (.abs 1 (.var 1)) ∧
    (Term.abs 0 (.var 0) : Term ℕ) =α (Term.abs 1 (.var 1)) :=
  ⟨rfl, alphaEquiv_iff_toLocallyNameless_eq.2 rfl⟩

/-- T-e: `λ0.1` and `λ1.1` have different translations, so by clause 2 they are not
α-equivalent. -/
example : toLocallyNameless (.abs 0 (.var 1) : Term ℕ) ≠ toLocallyNameless (.abs 1 (.var 1)) ∧
    ¬ ((Term.abs 0 (.var 1) : Term ℕ) =α (Term.abs 1 (.var 1))) :=
  have h : toLocallyNameless (.abs 0 (.var 1) : Term ℕ) ≠ toLocallyNameless (.abs 1 (.var 1)) := by
    decide
  ⟨h, fun hα => h (toLocallyNameless_eq_of_alphaEquiv hα)⟩

/-- T-f: by clause 1, `abs (bvar 1)`, which is not locally closed, is the translation of no
named term. -/
example (m : Term ℕ) : toLocallyNameless m ≠ .abs (.bvar 1) := by
  intro h
  have hlc := toLocallyNameless_lc m
  rw [h, ← LocallyNameless.Untyped.Term.lcAt_iff_LC] at hlc
  exact absurd hlc (by decide)

/-- Clause 1 needs no fresh name: it holds over `Unit`. -/
example : (toLocallyNameless (.abs () (.var ()) : Term Unit)).LC := toLocallyNameless_lc _

/-! ### Controls -/

/-- A translation that does not close binders. -/
private def noClose : Term ℕ → LocallyNameless.Untyped.Term ℕ
  | .var x => .fvar x
  | .abs _ m => .abs (noClose m)
  | .app m n => .app (noClose m) (noClose n)

/-- T-g (control): `noClose` sends the α-equivalent terms `λ0.0` and `λ1.1` to different terms,
so it violates clause 2. -/
example : ¬ ∀ m n : Term ℕ, m =α n ↔ noClose m = noClose n := fun h =>
  absurd ((h (.abs 0 (.var 0)) (.abs 1 (.var 1))).1
    (Term.AlphaEquiv.abs (y := 2) (by decide) Term.AlphaEquiv.var)) (by decide)

/-- T-h (control): over `Unit` no name is fresh, so `λ().()` is not α-equivalent to itself
although both sides have the same translation. Without `[HasFresh Var]`, injectivity
(`alphaEquiv_of_toLocallyNameless_eq`) fails. -/
example : ¬ ∀ m n : Term Unit, toLocallyNameless m = toLocallyNameless n → m =α n := by
  intro h
  have hα := h (.abs () (.var ())) (.abs () (.var ())) rfl
  rw [Term.AlphaEquiv_def] at hα
  cases hα with
  | abs hy _ => exact hy (by simp)

/-- The paired control for clause 3: over `Unit` the term `abs (bvar 1)` is locally closed, since
the rule `LC.abs` quantifies over the names outside `{()}` and there are none, but it is the
translation of no named term. Without `[HasFresh Var]`, surjectivity
(`exists_toLocallyNameless_eq`) fails. -/
example : ¬ ∀ t : LocallyNameless.Untyped.Term Unit, t.LC → ∃ m, toLocallyNameless m = t := by
  intro h
  obtain ⟨m, hm⟩ := h (.abs (.bvar 1))
    (.abs {()} _ fun _ hx => absurd (Finset.mem_singleton.2 rfl) hx)
  rcases m with _ | ⟨⟨⟩, ⟨⟩ | ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ <;> nomatch hm

/-- Over `Unit` surjectivity fails even on a term all of whose indices are in scope: `λx.λy.x`,
that is `abs (abs (bvar 1))`, is no translation, since with one name the inner binder always
shadows the outer one. -/
example : LcAt 0 (.abs (.abs (.bvar 1)) : LocallyNameless.Untyped.Term Unit) ∧
    ∀ m : Term Unit, toLocallyNameless m ≠ .abs (.abs (.bvar 1)) := by
  refine ⟨by decide, fun m hm => ?_⟩
  rcases m with _ | ⟨⟨⟩, ⟨⟩ | ⟨⟨⟩, ⟨⟩ | ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ <;> nomatch hm

/-- `fv_toLocallyNameless` is a simp lemma. -/
example (m : Term ℕ) : (toLocallyNameless m).fv = m.fv := by simp

/-! ### Signatures of the public declarations -/

example : ∀ {Var : Type u} [DecidableEq Var], Term Var → LocallyNameless.Untyped.Term Var :=
  @toLocallyNameless

example : ∀ {Var : Type u} [DecidableEq Var] (m : Term Var),
    (toLocallyNameless m).fv = m.fv :=
  @fv_toLocallyNameless

example : ∀ {Var : Type u} [DecidableEq Var] {x y : Var} {k : ℕ}
    {t : LocallyNameless.Untyped.Term Var}, y ∉ t.fv → (t[x := fvar y])⟦k ↜ y⟧ = t⟦k ↜ x⟧ :=
  @closeRec_subst_fvar_self

example : ∀ {Var : Type u} [DecidableEq Var] {x y z : Var} {k : ℕ}
    {t : LocallyNameless.Untyped.Term Var},
    z ≠ x → z ≠ y → (t[x := fvar y])⟦k ↜ z⟧ = (t⟦k ↜ z⟧)[x := fvar y] :=
  @closeRec_subst_fvar_of_ne

example : ∀ {Var : Type u} [DecidableEq Var] {x : Var} {k : ℕ}
    {t : LocallyNameless.Untyped.Term Var}, t.LcAt k → (t⟦k ↜ x⟧).LcAt (k + 1) :=
  @lcAt_succ_closeRec

example : ∀ {Var : Type u} [DecidableEq Var] {x y : Var} {m : Term Var},
    y ∉ m.vars → toLocallyNameless (m.rename x y) = (toLocallyNameless m)[x := fvar y] :=
  @toLocallyNameless_rename

example : ∀ {Var : Type u} [DecidableEq Var] (m : Term Var), (toLocallyNameless m).LC :=
  @toLocallyNameless_lc

example : ∀ {Var : Type u} [DecidableEq Var] {m n : Term Var},
    m =α n → toLocallyNameless m = toLocallyNameless n :=
  @toLocallyNameless_eq_of_alphaEquiv

example : ∀ {Var : Type u} [DecidableEq Var] [HasFresh Var] {m n : Term Var},
    toLocallyNameless m = toLocallyNameless n → m =α n :=
  @alphaEquiv_of_toLocallyNameless_eq

example : ∀ {Var : Type u} [DecidableEq Var] [HasFresh Var] {m n : Term Var},
    m =α n ↔ toLocallyNameless m = toLocallyNameless n :=
  @alphaEquiv_iff_toLocallyNameless_eq

example : ∀ {Var : Type u} [DecidableEq Var] [HasFresh Var]
    {t : LocallyNameless.Untyped.Term Var}, t.LC → ∃ m, toLocallyNameless m = t :=
  @exists_toLocallyNameless_eq

example : ∀ {Var : Type u} [DecidableEq Var] [HasFresh Var],
    (∀ m : Term Var, (toLocallyNameless m).LC) ∧
      (∀ m n : Term Var, m =α n ↔ toLocallyNameless m = toLocallyNameless n) ∧
      (∀ t : LocallyNameless.Untyped.Term Var, t.LC → ∃ m, toLocallyNameless m = t) :=
  @toLocallyNameless_relational_bijection

/-- The third clause applied to a concrete locally closed term. -/
example : ∃ m : Term ℕ,
    toLocallyNameless m = .abs (.app (.bvar 0) (.fvar 5)) :=
  (toLocallyNameless_relational_bijection (Var := ℕ)).2.2 _
    ((LocallyNameless.Untyped.Term.lcAt_iff_LC _).1 (by decide))

end Cslib.LambdaCalculus.Named.Untyped.LocallyNamelessBridgeTests
