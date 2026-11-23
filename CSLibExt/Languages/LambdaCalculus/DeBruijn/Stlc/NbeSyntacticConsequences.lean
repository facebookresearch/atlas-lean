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
# Consequences of syntactic completeness for STLC NbE
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeSyntacticCompleteness

/-!
# Canonical consequences of syntactic completeness

Completeness identifies declarative beta-eta conversion, equality under NbE,
and equality of eta-long normal forms.  This file packages that identification
as a practical API for canonical representatives, quotients, renaming, and
substitution.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B : Ty Base}
variable {Γ Δ Θ : List (Ty Base)}

namespace BetaEtaEq

/-- Declarative conversion is exactly observational NbE equality. -/
theorem iff_nbeEq {t u : Tm Γ A} : BetaEtaEq t u ↔ NbeEq t u := by
  rw [NbeEq.iff_normalizeTm_eq]
  exact betaEtaEq_iff_normalizeTm_eq

/-- Conversion can be checked at the normal-form syntax level. -/
theorem iff_normalizeNf_eq {t u : Tm Γ A} :
    BetaEtaEq t u ↔ normalizeNf t = normalizeNf u := by
  change BetaEtaEq t u ↔ NbeEq t u
  exact iff_nbeEq

/-- A term and its normal form represent the same declarative class. -/
theorem normalize_right (t : Tm Γ A) : BetaEtaEq t (normalizeTm t) :=
  betaEtaEq_normalizeTm t

/-- Normalization may also be used in the reverse direction. -/
theorem normalize_left (t : Tm Γ A) : BetaEtaEq (normalizeTm t) t :=
  (normalize_right t).symm

/-- Normalizing either endpoint preserves and reflects conversion. -/
theorem normalize_left_iff {t u : Tm Γ A} :
    BetaEtaEq (normalizeTm t) u ↔ BetaEtaEq t u := by
  constructor
  · exact fun h => (normalize_right t).trans h
  · exact fun h => (normalize_left t).trans h

/-- Normalizing the right endpoint preserves and reflects conversion. -/
theorem normalize_right_iff {t u : Tm Γ A} :
    BetaEtaEq t (normalizeTm u) ↔ BetaEtaEq t u := by
  constructor
  · exact fun h => h.trans (normalize_left u)
  · exact fun h => h.trans (normalize_right u)

/-- Both endpoints may be normalized without changing convertibility. -/
theorem normalize_both_iff {t u : Tm Γ A} :
    BetaEtaEq (normalizeTm t) (normalizeTm u) ↔ BetaEtaEq t u := by
  rw [normalize_left_iff, normalize_right_iff]

/-- Conversion to a canonical term determines that canonical term uniquely. -/
theorem canonical_eq_normalizeTm {t c : Tm Γ A}
    (hc : IsCanonical c) (h : BetaEtaEq t c) : c = normalizeTm t := by
  apply NbeEq.canonical_unique t c hc
  exact iff_nbeEq.mp h

/-- Two canonical beta-eta-convertible terms are syntactically equal. -/
theorem eq_of_isCanonical {t u : Tm Γ A} (ht : IsCanonical t)
    (hu : IsCanonical u) (h : BetaEtaEq t u) : t = u :=
  NbeEq.eq_of_isCanonical ht hu (iff_nbeEq.mp h)

/-- Erasures of eta-long normal forms are convertible exactly when the normal
forms themselves are equal. -/
theorem nf_toTm_iff_eq {n m : Nf Γ A} :
    BetaEtaEq n.toTm m.toTm ↔ n = m := by
  constructor
  · intro h
    apply Nf.toTm_injective
    exact eq_of_isCanonical ⟨n, rfl⟩ ⟨m, rfl⟩ h
  · exact fun h => h ▸ .refl _

/-- Renaming reflects beta-eta conversion whenever the renaming has a left
inverse. -/
theorem of_rename_of_leftInverse {t u : Tm Γ A} (ρ : Ren Γ Δ)
    (σ : Ren Δ Γ) (hleft : ∀ {B} (x : Var Γ B), σ (ρ x) = x)
    (h : BetaEtaEq (Tm.rename ρ t) (Tm.rename ρ u)) : BetaEtaEq t u := by
  have hs := h.rename σ
  rw [Tm.rename_comp, Tm.rename_comp] at hs
  have ht : Tm.rename (Var.comp ρ σ) t = t := by
    calc
      Tm.rename (Var.comp ρ σ) t = Tm.rename Var.id t :=
        Tm.rename_congr hleft t
      _ = t := Tm.rename_id t
  have hu : Tm.rename (Var.comp ρ σ) u = u := by
    calc
      Tm.rename (Var.comp ρ σ) u = Tm.rename Var.id u :=
        Tm.rename_congr hleft u
      _ = u := Tm.rename_id u
  exact (BetaEtaEq.of_eq ht.symm).trans (hs.trans (BetaEtaEq.of_eq hu))

/-- Substitution reflects beta-eta conversion whenever it has a syntactic
left inverse. -/
theorem of_subst_of_leftInverse {t u : Tm Γ A} (σ : Sub Γ Δ)
    (τ : Sub Δ Γ)
    (hleft : ∀ {B} (x : Var Γ B), BetaEtaEq (Tm.subst τ (σ x)) (.var x))
    (h : BetaEtaEq (Tm.subst σ t) (Tm.subst σ u)) : BetaEtaEq t u := by
  have hs := h.subst τ
  have ht : BetaEtaEq (Tm.subst τ (Tm.subst σ t)) t := by
    rw [Tm.subst_subst]
    exact (BetaEtaEq.subst_congr_right t hleft).trans
      (BetaEtaEq.of_eq (Tm.subst_id t))
  have hu : BetaEtaEq (Tm.subst τ (Tm.subst σ u)) u := by
    rw [Tm.subst_subst]
    exact (BetaEtaEq.subst_congr_right u hleft).trans
      (BetaEtaEq.of_eq (Tm.subst_id u))
  exact ht.symm.trans (hs.trans hu)

end BetaEtaEq

namespace NbeEq

/-- NbE equality implies and is implied by declarative conversion. -/
theorem iff_betaEtaEq {t u : Tm Γ A} : NbeEq t u ↔ BetaEtaEq t u :=
  BetaEtaEq.iff_nbeEq.symm

/-- Completeness turns NbE equality into a congruence under every typed term
context, not merely applications and abstractions exposed individually. -/
theorem context (C : TmCtx Γ A Δ B) {t u : Tm Γ A}
    (h : NbeEq t u) : NbeEq (C.plug t) (C.plug u) :=
  iff_betaEtaEq.mpr (BetaEtaEq.context C (iff_betaEtaEq.mp h))

/-- Completeness also makes simultaneous substitution jointly congruent in
the source term and all substitution images. -/
theorem subst_congr {t u : Tm Γ A} {σ τ : Sub Γ Δ}
    (htu : NbeEq t u) (hστ : ∀ {B} (x : Var Γ B), NbeEq (σ x) (τ x)) :
    NbeEq (Tm.subst σ t) (Tm.subst τ u) := by
  apply iff_betaEtaEq.mpr
  apply BetaEtaEq.subst_congr (iff_betaEtaEq.mp htu)
  exact fun x => iff_betaEtaEq.mp (hστ x)

/-- Pointwise NbE-equivalent substitutions act identically on every term. -/
theorem subst_pointwise (t : Tm Γ A) {σ τ : Sub Γ Δ}
    (h : ∀ {B} (x : Var Γ B), NbeEq (σ x) (τ x)) :
    NbeEq (Tm.subst σ t) (Tm.subst τ t) :=
  subst_congr (refl t) h

end NbeEq

/-! ## Quotients and canonical representatives -/

/-- Beta-eta classes and NbE observational classes are unconditionally
equivalent now that syntactic completeness has been established. -/
noncomputable def betaEtaEquivNbeClass :
    Equiv (BetaEtaClass Base Γ A) (NbeClass Base Γ A) :=
  Equiv.ofBijective
    (betaEtaToNbe (Base := Base) (Γ := Γ) (A := A))
    ⟨betaEtaComplete_iff_injective.mp betaEtaComplete,
      betaEtaToNbe_surjective⟩

@[simp] theorem betaEtaEquivNbeClass_apply (q : BetaEtaClass Base Γ A) :
    betaEtaEquivNbeClass q = betaEtaToNbe q := rfl

/-- Beta-eta classes are equivalent to eta-long normal forms. -/
noncomputable def betaEtaEquivNf :
    Equiv (BetaEtaClass Base Γ A) (Nf Γ A) :=
  betaEtaEquivNormalForm betaEtaComplete

/-- Every beta-eta class is represented by its observed normal form. -/
theorem betaEtaClass_eq_of_normalForm (q : BetaEtaClass Base Γ A) :
    q = BetaEtaClass.ofTm (BetaEtaClass.normalForm q).toTm :=
  betaEtaClass_eq_normalizeTm betaEtaComplete q

/-- The normal-form embedding is a bijection onto beta-eta classes. -/
theorem betaEtaNormalForm_bijective :
    Function.Bijective
      (fun n : Nf Γ A => BetaEtaClass.ofTm n.toTm) :=
  ⟨betaEtaNormalForm_injective,
    betaEtaNormalForm_surjective betaEtaComplete⟩

/-- Equality of beta-eta classes is reflected by their normal forms. -/
theorem betaEtaClass_eq_iff_normalForm_eq {q r : BetaEtaClass Base Γ A} :
    q = r ↔ BetaEtaClass.normalForm q = BetaEtaClass.normalForm r := by
  constructor
  · exact congrArg BetaEtaClass.normalForm
  · exact betaEtaComplete_iff_normalForm_reflects.mp betaEtaComplete q r

/-- The canonical map from declarative to observational quotients is now an
equivalence embedding. -/
theorem betaEtaToNbe_injective :
    Function.Injective
      (betaEtaToNbe (Base := Base) (Γ := Γ) (A := A)) :=
  betaEtaComplete_iff_injective.mp betaEtaComplete

/-- The canonical map from declarative to observational quotients is a
bijection. -/
theorem betaEtaToNbe_bijective :
    Function.Bijective
      (betaEtaToNbe (Base := Base) (Γ := Γ) (A := A)) :=
  ⟨betaEtaToNbe_injective, betaEtaToNbe_surjective⟩

end Cslib.Languages.LambdaCalculus.Stlc
