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
# Deciding beta-eta conversion by normalization
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeSyntacticConsequences

/-!
# Deciding beta-eta conversion

Syntactic completeness turns equality of computed eta-long normal forms into
a decision procedure for declarative beta-eta conversion.  This module first
provides structural equality procedures for the intrinsically indexed syntax,
then exposes executable boolean and decidable-proposition interfaces.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable [DecidableEq Base]
variable {A B : Ty Base}
variable {Γ Δ : List (Ty Base)}

deriving instance DecidableEq for Var
deriving instance DecidableEq for Tm
deriving instance DecidableEq for Ne
deriving instance DecidableEq for Nf

/-- Boolean beta-eta equivalence obtained by comparing computed normal forms. -/
def betaEtaEquivalent (t u : Tm Γ A) : Bool :=
  decide (normalizeNf t = normalizeNf u)

@[simp] theorem betaEtaEquivalent_eq_true {t u : Tm Γ A} :
    betaEtaEquivalent t u = true ↔ BetaEtaEq t u := by
  rw [betaEtaEquivalent, decide_eq_true_eq]
  exact BetaEtaEq.iff_normalizeNf_eq.symm

@[simp] theorem betaEtaEquivalent_eq_false {t u : Tm Γ A} :
    betaEtaEquivalent t u = false ↔ ¬ BetaEtaEq t u := by
  rw [Bool.eq_false_iff]
  exact not_congr betaEtaEquivalent_eq_true

/-- Declarative beta-eta conversion is decidable by NbE. -/
instance instDecidableBetaEtaEq (t u : Tm Γ A) : Decidable (BetaEtaEq t u) :=
  decidable_of_iff (normalizeNf t = normalizeNf u)
    BetaEtaEq.iff_normalizeNf_eq.symm

/-- The decision procedure accepts reflexivity. -/
@[simp] theorem betaEtaEquivalent_refl (t : Tm Γ A) :
    betaEtaEquivalent t t = true :=
  betaEtaEquivalent_eq_true.mpr (.refl t)

/-- The decision procedure is symmetric. -/
theorem betaEtaEquivalent_comm (t u : Tm Γ A) :
    betaEtaEquivalent t u = betaEtaEquivalent u t := by
  apply Bool.eq_iff_iff.mpr
  simp only [betaEtaEquivalent_eq_true]
  exact ⟨BetaEtaEq.symm, BetaEtaEq.symm⟩

/-- A positive decision is transitive. -/
theorem betaEtaEquivalent_trans {t u v : Tm Γ A}
    (htu : betaEtaEquivalent t u = true)
    (huv : betaEtaEquivalent u v = true) :
    betaEtaEquivalent t v = true :=
  betaEtaEquivalent_eq_true.mpr
    ((betaEtaEquivalent_eq_true.mp htu).trans
      (betaEtaEquivalent_eq_true.mp huv))

/-- Renaming preserves a positive beta-eta decision. -/
theorem betaEtaEquivalent_rename {t u : Tm Γ A}
    (h : betaEtaEquivalent t u = true) (ρ : Ren Γ Δ) :
    betaEtaEquivalent (Tm.rename ρ t) (Tm.rename ρ u) = true :=
  betaEtaEquivalent_eq_true.mpr ((betaEtaEquivalent_eq_true.mp h).rename ρ)

/-- Substitution preserves a positive beta-eta decision. -/
theorem betaEtaEquivalent_subst {t u : Tm Γ A}
    (h : betaEtaEquivalent t u = true) (σ : Sub Γ Δ) :
    betaEtaEquivalent (Tm.subst σ t) (Tm.subst σ u) = true :=
  betaEtaEquivalent_eq_true.mpr ((betaEtaEquivalent_eq_true.mp h).subst σ)

/-- Plugging positively equivalent terms into a typed context preserves the
decision. -/
theorem betaEtaEquivalent_context (C : TmCtx Γ A Δ B) {t u : Tm Γ A}
    (h : betaEtaEquivalent t u = true) :
    betaEtaEquivalent (C.plug t) (C.plug u) = true :=
  betaEtaEquivalent_eq_true.mpr
    (BetaEtaEq.context C (betaEtaEquivalent_eq_true.mp h))

/-- Normalization does not change the result of comparison on the left. -/
@[simp] theorem betaEtaEquivalent_normalize_left (t u : Tm Γ A) :
    betaEtaEquivalent (normalizeTm t) u = betaEtaEquivalent t u := by
  apply Bool.eq_iff_iff.mpr
  simp only [betaEtaEquivalent_eq_true, BetaEtaEq.normalize_left_iff]

/-- Normalization does not change the result of comparison on the right. -/
@[simp] theorem betaEtaEquivalent_normalize_right (t u : Tm Γ A) :
    betaEtaEquivalent t (normalizeTm u) = betaEtaEquivalent t u := by
  apply Bool.eq_iff_iff.mpr
  simp only [betaEtaEquivalent_eq_true, BetaEtaEq.normalize_right_iff]

/-- Comparing two normal forms is equivalent to structural equality. -/
theorem betaEtaEquivalent_nf_toTm (n m : Nf Γ A) :
    betaEtaEquivalent n.toTm m.toTm = decide (n = m) := by
  apply Bool.eq_iff_iff.mpr
  simp only [betaEtaEquivalent_eq_true, decide_eq_true_eq,
    BetaEtaEq.nf_toTm_iff_eq]

end Cslib.Languages.LambdaCalculus.Stlc
