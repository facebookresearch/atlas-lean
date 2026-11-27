/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Untyped.LocallyNamelessBridge

@[expose] public section

/-!
# Client tests for de Bruijn terms as locally nameless terms

Concrete translations in both directions, among them the examples of A. Charguéraud, *The locally
nameless representation*, Sections 2.3 and 2.4; the order of the naming context; a β-substitution;
and the bijection and the opening lemma on concrete terms.

Each hypothesis control takes an instance where the other hypotheses hold and the dropped one
fails, and shows that the conclusion fails: repeated names in the context, a free name outside the
context, a dangling bound variable, an unscoped term, a type of names without fresh elements, an
unscoped body or argument of a β-substitution, and an unscoped shifted term.
-/

namespace Cslib.LambdaCalculus.DeBruijn.Untyped.LocallyNamelessBridgeTests

open Cslib.Languages.LambdaCalculus.CEK (Tm)
open Cslib.LambdaCalculus.LocallyNameless.Untyped (Term)
open Cslib.LambdaCalculus.DeBruijn.Untyped.LocallyNamelessBridge
open scoped Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

/-! ### Concrete translations -/

/-- `λ. 0` is `abs (bvar 0)`. -/
example : toLocallyNameless ([] : List ℕ) (.lam (.var 0)) = .abs (.bvar 0) := rfl

/-- `λ. 0 1` in the context `[y]` is `λx. x y`, that is `abs (app (bvar 0) (fvar y))`. -/
example (y : ℕ) :
    toLocallyNameless [y] (.lam (.app (.var 0) (.var 1))) = .abs (.app (.bvar 0) (.fvar y)) :=
  rfl

/-- `λ. ((λ. 0 1) 0)` is `abs (app (abs (app (bvar 0) (bvar 1))) (bvar 0))`: the inner index `1`
is the outer bound variable. -/
example :
    toLocallyNameless ([] : List ℕ) (.lam (.app (.lam (.app (.var 0) (.var 1))) (.var 0))) =
      .abs (.app (.abs (.app (.bvar 0) (.bvar 1))) (.bvar 0)) :=
  rfl

/-- In the context `[7]`, `abs (app (bvar 0) (fvar 7))` translates back to `λ. 0 1`. -/
example :
    ofLocallyNameless [7] (.abs (.app (.bvar 0) (.fvar 7)) : Term ℕ) =
      .lam (.app (.var 0) (.var 1)) :=
  rfl

/-- The head of the context is the innermost free name: the index `0` is `fvar 1` in the
context `[1, 2]`. -/
example : toLocallyNameless [1, 2] (.var 0) = (.fvar 1 : Term ℕ) := rfl

/-- The index `0` is `fvar 2` in the context `[2, 1]`. -/
example : toLocallyNameless [2, 1] (.var 0) = (.fvar 2 : Term ℕ) := rfl

/-- A β-substitution in the context `[7]`: the contractum of `(λ. λ. 1) 0` translates to
`abs (fvar 7)`. -/
example :
    toLocallyNameless [7] (instantiate (.lam (.var 1)) (.var 0)) = (.abs (.fvar 7) : Term ℕ) :=
  rfl

/-- The translation of the body `λ. 1`, opened with the translation of the argument `0`, is the
same term `abs (fvar 7)`. -/
example :
    toLocallyNamelessAux 1 ([7] : List ℕ) (.lam (.var 1)) ^
        toLocallyNameless ([7] : List ℕ) (.var 0) =
      (.abs (.fvar 7) : Term ℕ) :=
  rfl

/-- Substituting an abstraction under a binder shifts only its free indices: the contractum of
`(λ. λ. 1) (λ. 0)` translates to `abs (abs (bvar 0))`. -/
example :
    toLocallyNameless ([] : List ℕ) (instantiate (.lam (.var 1)) (.lam (.var 0))) =
      .abs (.abs (.bvar 0)) :=
  rfl

/-! ### The bijection and the opening lemma on concrete terms -/

/-- The bijection sends `λ. 1`, scoped in the context `[7]`, to `abs (fvar 7)`. -/
example :
    ((equivLocallyNameless [7] (by decide)) ⟨.lam (.var 1), rfl⟩).val =
      (.abs (.fvar 7) : Term ℕ) :=
  rfl

/-- The inverse of the bijection sends `abs (fvar 7)` back to `λ. 1`. -/
example :
    ((equivLocallyNameless [7] (by decide)).symm
      ⟨.abs (.fvar 7), (Term.lcAt_iff_LC _).mp rfl, by simp⟩).val = .lam (.var 1) :=
  rfl

/-- The inverse undoes the bijection. -/
example (t : {t : Tm // scopedAt ([7] : List ℕ).length t}) :
    (equivLocallyNameless [7] (by decide)).symm (equivLocallyNameless [7] (by decide) t) = t :=
  Equiv.symm_apply_apply _ _

/-- The bijection for closed terms sends `λ. 0` to `abs (bvar 0)`. -/
example : (equivLocallyNamelessClosed (Var := ℕ) ⟨.lam (.var 0), rfl⟩).val = .abs (.bvar 0) :=
  rfl

/-- The translation of a scoped term is locally closed. -/
example : (toLocallyNameless [7] (.lam (.var 1)) : Term ℕ).LC := toLocallyNameless_lc rfl

/-- Opening the translation of the body `λ. 1` with `fvar 3` extends the context `[7]` to
`[3, 7]`. -/
example :
    toLocallyNamelessAux 1 ([7] : List ℕ) (.lam (.var 1)) ^ Term.fvar (3 : ℕ) =
      toLocallyNameless [3, 7] (.lam (.var 1)) :=
  open_toLocallyNameless_lam 3 [7] (.lam (.var 1))

/-- The β-substitution example, now by the theorem. -/
example :
    toLocallyNameless [7] (instantiate (.lam (.var 1)) (.var 0)) =
      toLocallyNamelessAux 1 ([7] : List ℕ) (.lam (.var 1)) ^
        toLocallyNameless ([7] : List ℕ) (.var 0) :=
  toLocallyNameless_instantiate rfl rfl

/-! ### Each hypothesis is needed -/

/-- Without `names.Nodup` the de Bruijn round trip fails: in the context `[0, 0]` the scoped term
`var 1` comes back as `var 0`. -/
example :
    ¬ ([0, 0] : List ℕ).Nodup ∧ scopedAt ([0, 0] : List ℕ).length (.var 1) ∧
      ofLocallyNameless [0, 0] (toLocallyNameless ([0, 0] : List ℕ) (.var 1)) ≠ .var 1 := by
  refine ⟨by decide, rfl, ?_⟩
  change Tm.var 0 ≠ Tm.var 1
  simp

/-- Without the membership of the free names in the context the locally nameless round trip
fails: `fvar 5` is locally closed, `5` is not in `[0]`, and `fvar 5` comes back as `bvar 1`. -/
example :
    (Term.fvar 5 : Term ℕ).LC ∧ ¬ (∀ x ∈ (Term.fvar 5 : Term ℕ).fv, x ∈ [0]) ∧
      toLocallyNameless [0] (ofLocallyNameless [0] (Term.fvar 5 : Term ℕ)) = .bvar 1 ∧
      toLocallyNameless [0] (ofLocallyNameless [0] (Term.fvar 5 : Term ℕ)) ≠ .fvar 5 :=
  ⟨.fvar 5, by simp, rfl, by decide⟩

/-- Without local closure the locally nameless round trip fails: the dangling `bvar 0` has no free
name, and in the context `[7]` it comes back as `fvar 7`. -/
example :
    (Term.bvar 0 : Term ℕ).LcAt 0 = false ∧ (∀ x ∈ (Term.bvar 0 : Term ℕ).fv, x ∈ [7]) ∧
      toLocallyNameless [7] (ofLocallyNameless [7] (Term.bvar 0 : Term ℕ)) = .fvar 7 ∧
      toLocallyNameless [7] (ofLocallyNameless [7] (Term.bvar 0 : Term ℕ)) ≠ .bvar 0 :=
  ⟨rfl, by simp, rfl, by decide⟩

/-- Without scoping the translation need not be locally closed: `lam (var 3)` is not scoped in the
empty context, and its translation `abs (bvar 3)` is not locally closed. -/
example :
    scopedAt ([] : List ℕ).length (.lam (.var 3)) = false ∧
      toLocallyNameless ([] : List ℕ) (.lam (.var 3)) = .abs (.bvar 3) ∧
      ¬ (toLocallyNameless ([] : List ℕ) (.lam (.var 3))).LC := by
  refine ⟨rfl, rfl, fun h => ?_⟩
  exact absurd ((Term.lcAt_iff_LC _).mpr h) (by decide)

/-- Without fresh names the bijection fails: over the one-element type `Unit` the cofinite rule
makes every abstraction locally closed, so `abs (bvar 5)` is locally closed without free names,
but its translation `lam (var 5)` is not scoped. -/
example :
    (Term.abs (.bvar 5) : Term Unit).LC ∧ (Term.abs (.bvar 5) : Term Unit).fv = ∅ ∧
      scopedAt ([] : List Unit).length (ofLocallyNameless [] (Term.abs (.bvar 5) : Term Unit)) =
        false :=
  ⟨.abs Finset.univ _ fun x hx => absurd (Finset.mem_univ x) hx, rfl, rfl⟩

/-- Without fresh names the locally nameless round trip fails too: over `Unit`, `abs (bvar 1)` is
locally closed and has no free name, but in the context `[()]` it comes back as
`abs (fvar ())`. -/
example :
    (Term.abs (.bvar 1) : Term Unit).LC ∧
      (∀ x ∈ (Term.abs (.bvar 1) : Term Unit).fv, x ∈ [()]) ∧
      toLocallyNameless [()] (ofLocallyNameless [()] (Term.abs (.bvar 1) : Term Unit)) =
        .abs (.fvar ()) ∧
      toLocallyNameless [()] (ofLocallyNameless [()] (Term.abs (.bvar 1) : Term Unit)) ≠
        .abs (.bvar 1) :=
  ⟨.abs Finset.univ _ fun x hx => absurd (Finset.mem_univ x) hx, by simp, rfl, by decide⟩

/-- Without scoping of the body β-substitution is not opening: in the empty context, with the
unscoped body `var 2` and the argument `var 0`, the two sides are `bvar 1` and `bvar 2`. -/
example :
    scopedAt (([] : List ℕ).length + 1) (.var 2) = false ∧
      toLocallyNameless ([] : List ℕ) (instantiate (.var 2) (.var 0)) = .bvar 1 ∧
      toLocallyNamelessAux 1 ([] : List ℕ) (.var 2) ^ toLocallyNameless [] (.var 0) = .bvar 2 :=
  ⟨rfl, rfl, rfl⟩

/-- The same failure with the scoped argument `λ. 0`, so that the scoping of the body is the only
hypothesis that fails. -/
example :
    scopedAt ([] : List ℕ).length (.lam (.var 0)) = true ∧
      scopedAt (([] : List ℕ).length + 1) (.var 2) = false ∧
      toLocallyNameless ([] : List ℕ) (instantiate (.var 2) (.lam (.var 0))) ≠
        toLocallyNamelessAux 1 ([] : List ℕ) (.var 2) ^ toLocallyNameless [] (.lam (.var 0)) :=
  ⟨rfl, rfl, by decide⟩

/-- Without scoping of the argument β-substitution is not opening: in the empty context the body
`λ. 1` is scoped at `1`, the argument `var 0` is not scoped, and the two sides are
`abs (bvar 1)` and `abs (bvar 0)`. -/
example :
    scopedAt (([] : List ℕ).length + 1) (.lam (.var 1)) = true ∧
      scopedAt ([] : List ℕ).length (.var 0) = false ∧
      toLocallyNameless ([] : List ℕ) (instantiate (.lam (.var 1)) (.var 0)) = .abs (.bvar 1) ∧
      toLocallyNamelessAux 1 ([] : List ℕ) (.lam (.var 1)) ^ toLocallyNameless [] (.var 0) =
        .abs (.bvar 0) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Without scoping, shifting is visible: `var 0` is not scoped in the empty context, and
`shift 1 0 (var 0)` translates one binder deeper to `bvar 1`, not to `bvar 0`. -/
example :
    scopedAt (0 + ([] : List ℕ).length) (.var 0) = false ∧
      toLocallyNamelessAux (1 + 0) ([] : List ℕ) (shift 1 0 (.var 0)) ≠
        toLocallyNamelessAux 0 ([] : List ℕ) (.var 0) :=
  ⟨rfl, by decide⟩

end Cslib.LambdaCalculus.DeBruijn.Untyped.LocallyNamelessBridgeTests
