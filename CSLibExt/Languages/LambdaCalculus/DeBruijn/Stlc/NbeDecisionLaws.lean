/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Algebraic laws of the STLC beta-eta decision procedure
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeQuotientDecision

/-!
# Algebraic laws of beta-eta comparison

The executable comparison respects every constructor and structural operation
of intrinsically typed STLC.  These laws let clients reason about the boolean
procedure compositionally without reopening its normalization definition.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u} [DecidableEq Base]
variable {A B C : Ty Base}
variable {Γ Δ : List (Ty Base)}

/-- Equivalent functions applied to equivalent arguments remain equivalent. -/
theorem betaEtaEquivalent_app {f g : Tm Γ (A ⇒ B)} {a b : Tm Γ A}
    (hf : betaEtaEquivalent f g = true)
    (ha : betaEtaEquivalent a b = true) :
    betaEtaEquivalent (.app f a) (.app g b) = true :=
  betaEtaEquivalent_eq_true.mpr
    (.app (betaEtaEquivalent_eq_true.mp hf)
      (betaEtaEquivalent_eq_true.mp ha))

/-- Equivalent bodies remain equivalent under abstraction. -/
theorem betaEtaEquivalent_lam {t u : Tm (A :: Γ) B}
    (h : betaEtaEquivalent t u = true) :
    betaEtaEquivalent (.lam t) (.lam u) = true :=
  betaEtaEquivalent_eq_true.mpr (.lam (betaEtaEquivalent_eq_true.mp h))

/-- The comparison procedure validates beta reduction. -/
@[simp] theorem betaEtaEquivalent_beta (body : Tm (A :: Γ) B)
    (a : Tm Γ A) :
    betaEtaEquivalent (.app (.lam body) a) (Tm.instantiate body a) = true :=
  betaEtaEquivalent_eq_true.mpr (.beta body a)

/-- The comparison procedure validates eta reduction. -/
@[simp] theorem betaEtaEquivalent_eta (f : Tm Γ (A ⇒ B)) :
    betaEtaEquivalent
      (.lam (.app (Tm.weaken f) (.var .zero))) f = true :=
  betaEtaEquivalent_eq_true.mpr (.eta f)

/-- Equivalent open bodies remain equivalent after instantiation by the same
argument. -/
theorem betaEtaEquivalent_instantiate {t u : Tm (A :: Γ) B}
    (h : betaEtaEquivalent t u = true) (a : Tm Γ A) :
    betaEtaEquivalent (Tm.instantiate t a) (Tm.instantiate u a) = true :=
  betaEtaEquivalent_eq_true.mpr
    ((betaEtaEquivalent_eq_true.mp h).instantiate a)

/-- Instantiating one body with equivalent arguments yields equivalent terms. -/
theorem betaEtaEquivalent_instantiate_arg (body : Tm (A :: Γ) B)
    {a b : Tm Γ A} (h : betaEtaEquivalent a b = true) :
    betaEtaEquivalent (Tm.instantiate body a) (Tm.instantiate body b) = true :=
  betaEtaEquivalent_eq_true.mpr
    (BetaEtaEq.instantiate_arg body (betaEtaEquivalent_eq_true.mp h))

/-- Instantiation is jointly congruent in the body and argument. -/
theorem betaEtaEquivalent_instantiate_congr {t u : Tm (A :: Γ) B}
    {a b : Tm Γ A} (ht : betaEtaEquivalent t u = true)
    (ha : betaEtaEquivalent a b = true) :
    betaEtaEquivalent (Tm.instantiate t a) (Tm.instantiate u b) = true :=
  betaEtaEquivalent_eq_true.mpr
    (BetaEtaEq.instantiate_congr (betaEtaEquivalent_eq_true.mp ht)
      (betaEtaEquivalent_eq_true.mp ha))

/-- Pointwise equivalent substitutions act equivalently on every term. -/
theorem betaEtaEquivalent_subst_pointwise (t : Tm Γ A)
    {σ τ : Sub Γ Δ}
    (h : ∀ {B} (x : Var Γ B), betaEtaEquivalent (σ x) (τ x) = true) :
    betaEtaEquivalent (Tm.subst σ t) (Tm.subst τ t) = true := by
  apply betaEtaEquivalent_eq_true.mpr
  apply BetaEtaEq.subst_pointwise
  exact fun x => betaEtaEquivalent_eq_true.mp (h x)

/-- Substitution is jointly congruent in its term and environment. -/
theorem betaEtaEquivalent_subst_congr {t u : Tm Γ A} {σ τ : Sub Γ Δ}
    (htu : betaEtaEquivalent t u = true)
    (hστ : ∀ {B} (x : Var Γ B), betaEtaEquivalent (σ x) (τ x) = true) :
    betaEtaEquivalent (Tm.subst σ t) (Tm.subst τ u) = true := by
  apply betaEtaEquivalent_eq_true.mpr
  apply BetaEtaEq.subst_congr (betaEtaEquivalent_eq_true.mp htu)
  exact fun x => betaEtaEquivalent_eq_true.mp (hστ x)

/-- A one-step beta-eta contraction is accepted by the comparison. -/
theorem BetaEtaStep.betaEtaEquivalent {t u : Tm Γ A}
    (h : BetaEtaStep t u) : betaEtaEquivalent t u = true :=
  betaEtaEquivalent_eq_true.mpr h.betaEtaEq

/-- Every finite contraction sequence is accepted by the comparison. -/
theorem BetaEtaSteps.betaEtaEquivalent {t u : Tm Γ A}
    (h : BetaEtaSteps t u) : betaEtaEquivalent t u = true :=
  betaEtaEquivalent_eq_true.mpr h.betaEtaEq

/-- Joinable terms are accepted by the comparison. -/
theorem BetaEtaJoin.betaEtaEquivalent {t u : Tm Γ A}
    (h : BetaEtaJoin t u) : betaEtaEquivalent t u = true :=
  betaEtaEquivalent_eq_true.mpr h.betaEtaEq

/-- A beta-eta zigzag is accepted by the comparison. -/
theorem BetaEtaZigzag.betaEtaEquivalent {t u : Tm Γ A}
    (h : BetaEtaZigzag t u) : betaEtaEquivalent t u = true :=
  betaEtaEquivalent_eq_true.mpr h.betaEtaEq

/-- Failure of comparison refutes every declarative conversion derivation. -/
theorem not_betaEtaEq_of_equivalent_eq_false {t u : Tm Γ A}
    (h : betaEtaEquivalent t u = false) : ¬ BetaEtaEq t u :=
  betaEtaEquivalent_eq_false.mp h

/-- Failure of comparison refutes one-step contraction. -/
theorem not_betaEtaStep_of_equivalent_eq_false {t u : Tm Γ A}
    (h : betaEtaEquivalent t u = false) : ¬ BetaEtaStep t u :=
  fun step => not_betaEtaEq_of_equivalent_eq_false h step.betaEtaEq

/-- Failure of comparison refutes every finite contraction sequence. -/
theorem not_betaEtaSteps_of_equivalent_eq_false {t u : Tm Γ A}
    (h : betaEtaEquivalent t u = false) : ¬ BetaEtaSteps t u :=
  fun steps => not_betaEtaEq_of_equivalent_eq_false h steps.betaEtaEq

/-- Failure of comparison refutes joinability. -/
theorem not_betaEtaJoin_of_equivalent_eq_false {t u : Tm Γ A}
    (h : betaEtaEquivalent t u = false) : ¬ BetaEtaJoin t u :=
  fun join => not_betaEtaEq_of_equivalent_eq_false h join.betaEtaEq

/-- Failure of comparison refutes every beta-eta zigzag. -/
theorem not_betaEtaZigzag_of_equivalent_eq_false {t u : Tm Γ A}
    (h : betaEtaEquivalent t u = false) : ¬ BetaEtaZigzag t u :=
  fun zigzag => not_betaEtaEq_of_equivalent_eq_false h zigzag.betaEtaEq

end Cslib.Languages.LambdaCalculus.Stlc
