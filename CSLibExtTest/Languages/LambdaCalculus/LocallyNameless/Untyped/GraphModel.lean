/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.LocallyNameless.Untyped.GraphModel
public import Mathlib.Tactic

open MathlibExt.Order.ScottContinuity.GraphModel
open Cslib.LambdaCalculus.LocallyNameless.Untyped
open Cslib.LambdaCalculus.LocallyNameless.Untyped.GraphModel

/-- The identity `λ.0` applied to `v` denotes `v`. -/
example (ρ : ℕ → Set ℕ) (bs : ℕ → Set ℕ) (v : Set ℕ) :
    app (denote ρ (.abs (.bvar 0) : Term ℕ) bs) v = v :=
  app_denote_abs ρ _ bs v

/-- A concrete β-step `(λ.0) x ⟶ x` preserves denotations. -/
example (ρ : ℕ → Set ℕ) (bs : ℕ → Set ℕ) :
    denote ρ (.app (.abs (.bvar 0)) (.fvar 0) : Term ℕ) bs = denote ρ (.fvar 0) bs := by
  have h1 : Term.LC (.abs (.bvar 0) : Term ℕ) := (Term.lcAt_iff_LC _).1 (by decide)
  have h2 : Term.LC (.fvar 0 : Term ℕ) := Term.LC.fvar 0
  exact denote_eq_of_fullBeta (Term.Xi.base (Term.Beta.beta h1 h2)) ρ bs

/-- `K` and `K*` are separated (non-degeneracy). -/
example : denote (fun _ : ℕ => (∅ : Set ℕ)) (.abs (.abs (.bvar 1)) : Term ℕ)
    (fun _ : ℕ => (∅ : Set ℕ)) ≠
    denote (fun _ : ℕ => (∅ : Set ℕ)) (.abs (.abs (.bvar 0))) (fun _ : ℕ => (∅ : Set ℕ)) :=
  denote_K_ne_denote_KStar _ _

/-- `Y` applied to the empty set denotes the empty set. -/
example : app (denote (fun _ : ℕ => (∅ : Set ℕ)) (Y : Term ℕ) (fun _ : ℕ => (∅ : Set ℕ))) ∅ =
    ⨆ k, (app ∅)^[k] ⊥ :=
  app_denote_Y _ _ _

/-- η is not sound. -/
example : ∃ ρ : ℕ → Set ℕ,
    denote ρ (.abs (.app (.fvar 0) (.bvar 0)) : Term ℕ) (fun _ : ℕ => (∅ : Set ℕ)) ≠
      denote ρ (.fvar 0) (fun _ : ℕ => (∅ : Set ℕ)) :=
  exists_denote_eta_ne 0 _

/-- The denotation of `λy. x y` is Scott-continuous in the value of the free variable `x`. -/
example : ScottContinuous fun ρ : ℕ → Set ℕ =>
    denote ρ (.abs (.app (.fvar 0) (.bvar 0)) : Term ℕ) (fun _ => ∅) :=
  scottContinuous_denote_fvar _ _

/-- β-soundness under λ: the step `λ.((λ.0) 0) ⟶ λ.0`, which contracts a redex below a binder
(the `Xi.abs` case of full β-reduction), preserves denotations. -/
example (ρ : ℕ → Set ℕ) (bs : ℕ → Set ℕ) :
    denote ρ (.abs (.app (.abs (.bvar 0)) (.bvar 0)) : Term ℕ) bs =
      denote ρ (.abs (.bvar 0)) bs := by
  have h1 : Term.LC (.abs (.bvar 0) : Term ℕ) := (Term.lcAt_iff_LC _).1 (by decide)
  have hstep : Term.FullBeta (.abs (.app (.abs (.bvar 0)) (.bvar 0)) : Term ℕ) (.abs (.bvar 0)) :=
    Term.Xi.abs ∅ fun x _ => Term.Xi.base (Term.Beta.beta h1 (Term.LC.fvar x))
  exact denote_eq_of_fullBeta hstep ρ bs
