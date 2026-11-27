/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.LocallyNameless.Untyped.OmegaExamples

@[expose] public section

/-!
# Client tests for `Ω` and `K I Ω`

The theorems of `OmegaExamples` at the name type `ℕ`, the contractions they rest on (each holds by
`rfl`), a non-leftmost reduction of `K I Ω` that loops, and two counterexamples over the
one-element name type `Unit`, where the cofinite ξ-rule is vacuous: there `Ω` has a reduct other
than itself and `I` is not normal, so the `HasFresh` hypothesis cannot be dropped.
-/

namespace Cslib.LambdaCalculus.LocallyNameless.Untyped.OmegaExamplesTests

open Cslib.LambdaCalculus.LocallyNameless.Untyped
open Cslib.LambdaCalculus.LocallyNameless.Untyped.Term
open Cslib.LambdaCalculus.LocallyNameless.Untyped.OmegaExamples
open scoped Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

/-! ### The theorems at `Term ℕ` -/

example : (Omega : Term ℕ).LC ∧ (app (app K I) Omega : Term ℕ).LC := ⟨Omega_lc, KIOmega_lc⟩

example : (Omega : Term ℕ) ⭢βᶠ Omega := Omega_step_self

example (N : Term ℕ) (h : Omega ↠βᶠ N) : N = Omega := eq_Omega_of_steps N h

example : ¬ Relation.Normalizable FullBeta (Omega : Term ℕ) := not_normalizable_Omega

example : app (app K I) (Omega : Term ℕ) ↠ℓ I := KIOmega_leftmost_I

example : Relation.Normal FullBeta (I : Term ℕ) := normal_I

/-! ### The contractions are definitional -/

/-- Contracting `Ω = (λ. 0 0) ω` gives back `ω ω = Ω`. -/
example : (app (bvar 0) (bvar 0) : Term ℕ) ^ omega = Omega := rfl

/-- Contracting `K I` gives `λ. I`: the index `1` under one binder becomes `I`. -/
example : (abs (bvar 1) : Term ℕ) ^ I = abs I := rfl

/-- Contracting `(λ. I) Ω` discards `Ω`. -/
example : (I : Term ℕ) ^ Omega = I := rfl

/-- The decision procedure for local closure agrees with `KIOmega_lc` at `ℕ`. -/
example : (app (app K I) Omega : Term ℕ).LC :=
  (Term.lcAt_iff_LC (app (app K I) Omega)).mp (by decide)

/-! ### Reducing inside `Ω` instead loops -/

/-- `K I Ω` also reduces to itself, by contracting `Ω` in the argument position. -/
example : app (app K I) (Omega : Term ℕ) ⭢βᶠ app (app K I) Omega :=
  Xi.appL (.app K_lc I_lc) Omega_step_self

/-! ### Without fresh names the irreducibility statements fail -/

/-- Over `Unit`, `Finset.univ` excludes every name, so the ξ-rule makes any abstraction reduce to
any other. -/
theorem abs_fullBeta_abs_unit (M N : Term Unit) : abs M ⭢βᶠ abs N :=
  Xi.abs Finset.univ fun x hx => absurd (Finset.mem_univ x) hx

/-- Over `Unit`, `Ω` has a full β-reduct other than `Ω`, obtained by rewriting the operator `ω`. -/
example : ∃ N : Term Unit, Omega ⭢βᶠ N ∧ N ≠ Omega :=
  ⟨app (abs (fvar ())) omega,
    Xi.appR (.abs ∅ _ fun y _ => .app (.fvar y) (.fvar y)) (abs_fullBeta_abs_unit _ _),
    by decide⟩

/-- Over `Unit`, `I` is not a normal form. -/
example : ¬ Relation.Normal FullBeta (I : Term Unit) :=
  fun hI => hI ⟨abs (fvar ()), abs_fullBeta_abs_unit _ _⟩

end Cslib.LambdaCalculus.LocallyNameless.Untyped.OmegaExamplesTests
