/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.LocallyNameless.Untyped.NormalForm
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
public import Cslib.Foundations.Relation.Confluence

/-!
# Tests for relational β-normal forms of locally closed terms

Statement pins for every public declaration of
`CSLibExt.Languages.LambdaCalculus.LocallyNameless.Untyped.NormalForm`, the ill-scoped
counterexample showing that the local-closure hypothesis of `NormalForm.betaNormal_of_normal`
cannot be dropped, a finite-name control, concrete uses of each theorem, and agreement with the
uniqueness of relational normal forms.
-/

namespace CSLibExtTest.Languages.LambdaCalculus.LocallyNameless.Untyped.NormalFormTests

open Cslib.LambdaCalculus.LocallyNameless.Untyped
open Cslib.LambdaCalculus.LocallyNameless.Untyped.Term
open scoped Cslib.LambdaCalculus.LocallyNameless.Untyped.Term
open Cslib (HasFresh)

universe u

/-! ### Statement pins -/

/-- Pin for `NormalForm.betaNormal_of_normal`. -/
example {Var : Type u} [HasFresh Var] {M : Term Var} (lc : M.LC)
    (h : Relation.Normal FullBeta M) : M.BetaNormal :=
  NormalForm.betaNormal_of_normal lc h

/-- Pin for `NormalForm.leftmost_of_normal`. -/
example {Var : Type u} [HasFresh Var] {M N : Term Var} (lc : M.LC) (h : M ↠βᶠ N)
    (hn : Relation.Normal FullBeta N) : M ↠ℓ N :=
  NormalForm.leftmost_of_normal lc h hn

/-- Pin for `NormalForm.exists_leftmost_of_normalizable`. -/
example {Var : Type u} [HasFresh Var] {M : Term Var} (lc : M.LC)
    (h : Relation.Normalizable FullBeta M) : ∃ N, M ↠ℓ N ∧ Relation.Normal FullBeta N :=
  NormalForm.exists_leftmost_of_normalizable lc h

/-! ### T1: local closure cannot be dropped (acceptance A1) -/

/-- The redex `(λ. 0) 1`, whose argument is a dangling index. -/
private abbrev illScoped {Var : Type u} : Term Var := app (abs (bvar 0)) (bvar 1)

/-- The argument `bvar 1` is not locally closed, hence neither is the redex. -/
private theorem illScoped_not_lc {Var : Type u} : ¬ (illScoped : Term Var).LC := fun h =>
  match h with
  | .app _ hArg => nomatch hArg

/-- No full β-step leaves the ill-scoped redex: the β-rule and the right congruence rule need a
locally closed argument, and the left congruence rule needs a step of `bvar 1`. -/
private theorem illScoped_normal {Var : Type u} :
    Relation.Normal FullBeta (illScoped : Term Var) := by
  rw [Relation.normal_iff]
  intro N hstep
  match hstep with
  | .base (.beta _ hArg) => nomatch hArg
  | .appL _ hArgStep => match hArgStep with | .base hβ => nomatch hβ
  | .appR hArg _ => nomatch hArg

/-- The ill-scoped redex still counts as one syntactic redex. -/
private theorem illScoped_not_betaNormal {Var : Type u} : ¬ (illScoped : Term Var).BetaNormal :=
  fun h => absurd ((rfl : (illScoped : Term Var).countRedexes = 1).symm.trans h) Nat.one_ne_zero

/-- Acceptance A1: `NormalForm.betaNormal_of_normal` without its local-closure hypothesis fails,
for every type of names: the ill-scoped redex is relationally normal but not `BetaNormal`. -/
example {Var : Type u} : ¬ ∀ M : Term Var, Relation.Normal FullBeta M → M.BetaNormal :=
  fun hall => illScoped_not_betaNormal (hall _ illScoped_normal)

/-- The counterexample is exactly outside the hypothesis of `NormalForm.betaNormal_of_normal`. -/
example {Var : Type u} :
    ¬ (illScoped : Term Var).LC ∧ Relation.Normal FullBeta (illScoped : Term Var) :=
  ⟨illScoped_not_lc, illScoped_normal⟩

/-! ### Fresh names: a finite-name control and its counterpart over `ℕ` -/

/-- Over `Unit` the cofinite ξ-rule has no premise, so `λ. 0`, which contains no redex, steps to
`λ. ()`: relational normal forms of abstractions need fresh names (`HasFresh`). -/
example : (abs (bvar 0) : Term Unit).BetaNormal ∧
    ¬ Relation.Normal FullBeta (abs (bvar 0) : Term Unit) :=
  ⟨rfl, fun h => h ⟨abs (fvar ()), Xi.abs {()} fun x hx =>
    absurd (Finset.mem_singleton.mpr (Subsingleton.elim x ())) hx⟩⟩

/-- Over `ℕ` the same term has no full β-step: a step under the binder would be a step of the
free variable obtained by opening with a fresh name. -/
private theorem id_normal : Relation.Normal FullBeta (abs (bvar 0) : Term ℕ) := by
  rintro ⟨_, hstep⟩
  cases hstep with
  | base hβ => nomatch hβ
  | abs xs hbody =>
    obtain ⟨x, hx⟩ := Cslib.HasFresh.fresh_exists xs
    have hvar : Xi Beta (fvar x) _ := hbody x hx
    cases hvar with
    | base hβ => nomatch hβ

/-- A free variable has no full β-step. -/
private theorem fvar_normal : Relation.Normal FullBeta (fvar 0 : Term ℕ) := by
  rintro ⟨_, hstep⟩
  cases hstep with
  | base hβ => nomatch hβ

/-! ### T2-T5: the theorems on concrete terms -/

private theorem id_lc : (abs (bvar 0) : Term ℕ).LC := (lcAt_iff_LC _).1 (by decide)

/-- The redex `(λ. 0) x₀`. -/
private abbrev idApp : Term ℕ := app (abs (bvar 0)) (fvar 0)

private theorem idApp_lc : idApp.LC := LC.app id_lc (LC.fvar 0)

private theorem idApp_step : idApp ⭢βᶠ fvar 0 := Xi.base (Beta.beta id_lc (LC.fvar 0))

/-- T2: `NormalForm.betaNormal_of_normal` turns the relational normality of `λ. 0` over `ℕ` into
syntactic normality. -/
example : (abs (bvar 0) : Term ℕ).BetaNormal :=
  NormalForm.betaNormal_of_normal id_lc id_normal

/-- T2 boundary: the redex `(λ. 0) x₀` is not normal, so it is outside the hypothesis. -/
example : ¬ Relation.Normal FullBeta idApp := fun h => h ⟨_, idApp_step⟩

/-- T3: leftmost reduction takes `(λ. 0) x₀` to its relational normal form `x₀`. -/
example : idApp ↠ℓ fvar 0 :=
  NormalForm.leftmost_of_normal idApp_lc (.single idApp_step) fvar_normal

/-- Church-Rosser for full β-reduction, from CSLib's confluence theorem. -/
private theorem churchRosser_fullBeta {Var : Type u} [HasFresh Var] [DecidableEq Var] :
    Relation.ChurchRosser (FullBeta : Term Var → Term Var → Prop) :=
  Relation.Confluent.to_churchRosser confluent_fullBeta

/-- T4 (acceptance A2): relational normal forms are unique (`Relation.ChurchRosser.normal_eq`
with `confluent_fullBeta`), and leftmost reduction reaches that unique normal form. -/
example {Var : Type u} [HasFresh Var] [DecidableEq Var] {M N₁ N₂ : Term Var} (lc : M.LC)
    (h₁ : M ↠βᶠ N₁) (h₂ : M ↠βᶠ N₂) (n₁ : Relation.Normal FullBeta N₁)
    (n₂ : Relation.Normal FullBeta N₂) : N₁ = N₂ ∧ M ↠ℓ N₁ ∧ M ↠ℓ N₂ :=
  ⟨Relation.ChurchRosser.normal_eq churchRosser_fullBeta n₁ n₂
      (.trans _ _ _ (.symm _ _ h₁.to_eqvGen) h₂.to_eqvGen),
    NormalForm.leftmost_of_normal lc h₁ n₁, NormalForm.leftmost_of_normal lc h₂ n₂⟩

/-- Leftmost reduction from a locally closed term is full β-reduction. -/
private theorem fullBeta_of_leftmost {M N : Term ℕ} (lc : M.LC) (h : M ↠ℓ N) : M ↠βᶠ N := by
  induction h with
  | refl => exact .refl
  | tail hpre hstep ih => exact ih.tail (BetaAt.to_step hstep (Leftmost.steps_lc_r hpre lc))

/-- T5: `(λ. 0) x₀` has a relational normal form, so leftmost reduction reaches one, and by
uniqueness it is `x₀`. -/
example : ∃ N, idApp ↠ℓ N ∧ Relation.Normal FullBeta N ∧ N = fvar 0 := by
  obtain ⟨N, hlm, hN⟩ :=
    NormalForm.exists_leftmost_of_normalizable idApp_lc ⟨fvar 0, .single idApp_step, fvar_normal⟩
  refine ⟨N, hlm, hN, Relation.ChurchRosser.normal_eq churchRosser_fullBeta hN fvar_normal ?_⟩
  exact .trans _ _ _ (.symm _ _ (fullBeta_of_leftmost idApp_lc hlm).to_eqvGen)
    (Relation.ReflTransGen.single idApp_step).to_eqvGen

end CSLibExtTest.Languages.LambdaCalculus.LocallyNameless.Untyped.NormalFormTests
