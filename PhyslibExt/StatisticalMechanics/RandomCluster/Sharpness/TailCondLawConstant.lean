/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.TailCondLaw

/-!
# The tail conditional law from a constant switch

Randomized tail selection, its measure-preserving property, and the tail conditional law when the
stopping value is constant on each head.

## i. Overview

`atl_selRand` selects tail labels at the stopping value. `atl_TailSelMP` says that this selection is
measure preserving; under it the diagonal, marginal and cross terms are computed (`atl_diag_of_MP`,
`atl_marg_of_MP`, `atl_cross_of_MP_mono`). `atl_tailCondLaw_of_residues` assembles them.
`atl_tailCondLaw_const_switch` is conditional on `hconst`: the stopping value depends only on the
head `A`. The tail-selection files (`TailSelMP`, `TailSelMPRecovery`, `TailSelMPSplice`,
`OptionalStopping`) prove that the stopped tail selection is measure preserving, which
`TailCondLawConstant` turns into the tail conditional law. This file is one step of the OSSS chain
for monotonic measures: `AdaptMConditional` (OSSS from `AdaptStepCovBound`) ← `AdaptDisintegration`
(`AdaptCondBBB` ⇒ `AdaptStepCovBound`) ← `AdaptCondReduction` (`acp_TailCondLaw` ⇒ `AdaptCondBBB`) ←
`TailCondLawConstant` / `CrossMonotone` (`acp_TailCondLaw` for monotonic measures), assembled
unconditionally in `MonotoneOSSSAssembly.osss_monotone_sharp`.

## ii. Key results

- `atl_tailCondLaw_of_residues`: tail law from the measure-preserving residues.
- `atl_tailCondLaw_const_switch`: tail law, conditional on a head-determined stopping value.

## iii. Table of contents

- A. Randomized tail selection
- B. Diagonal, marginal and cross terms
- C. The tail law

## iv. References

* R. O'Donnell, M. Saks, O. Schramm, R. Servedio, *Every decision tree has an influential variable*,
  FOCS 2005.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Finset MeasureTheory


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly
open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## A. Randomized tail selection -/

/-- The randomized tail selection at step `t` and stopping value `s`, given the head `A`. -/
noncomputable def atl_selRand (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ)) : Fin n → ℝ :=
  adaptWt (acp_join t A p.1) p.2 (stopVal μ σ f (acp_join t A p.1)) s

/-- The randomized tail selection is measure preserving. -/
def atl_TailSelMP (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) : Prop :=
  MeasurePreserving (atl_selRand μ σ f t s A) ((ubfTail n t).prod (Vcube n)) (Vcube n)

lemma atl_jointMeas (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f g : ConfigSpace E → ℝ)
    (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (atl_selRand μ σ f t s A p))) := by
  have hjoin : Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      (acp_join t A p.1, p.2)) :=
    Measurable.prodMk
      ((ubfSplit n t).symm.measurable.comp (measurable_const.prodMk measurable_fst))
      measurable_snd
  exact (measurable_g_adaptWt μ σ f g s).comp hjoin

lemma atl_tailSelMP_of_stop_le {μ : ConfigSpace E → ℝ} {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (hstop : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) ≤ s) :
    atl_TailSelMP μ σ f t s A := by
  have heq : atl_selRand μ σ f t s A = Prod.snd := by
    funext p
    change adaptWt (acp_join t A p.1) p.2 (stopVal μ σ f (acp_join t A p.1)) s = p.2
    exact adaptWt_ge_stop _ _ _ s (hstop p.1)
  change MeasurePreserving (atl_selRand μ σ f t s A) ((ubfTail n t).prod (Vcube n)) (Vcube n)
  rw [heq]
  exact measurePreserving_snd

/-! ## B. Diagonal, marginal and cross terms -/

lemma atl_innerRand_eq_mean (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (g : ConfigSpace E → ℝ) {Cg : ℝ} (hgC : ∀ ω, |g ω| ≤ Cg) (t s : ℕ)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) (hMP : atl_TailSelMP μ σ f t s A) :
    (∫ B, (∫ V, g (codeMap μ (σ : Fin n → E)
            (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) s)) ∂(Vcube n))
        ∂(ubfTail n t))
      = Lindeberg.mean μ g := by
  have hint : Integrable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (atl_selRand μ σ f t s A p)))
      ((ubfTail n t).prod (Vcube n)) :=
    ContinuousFKG.integrable_of_bdd _ (atl_jointMeas μ σ f g t s A) (fun p => hgC _)
  have hfub : (∫ p, g (codeMap μ (σ : Fin n → E) (atl_selRand μ σ f t s A p))
        ∂((ubfTail n t).prod (Vcube n)))
      = ∫ B, (∫ V, g (codeMap μ (σ : Fin n → E)
            (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) s)) ∂(Vcube n))
          ∂(ubfTail n t) := by
    rw [integral_prod _ hint]; rfl
  have hmean : (∫ p, g (codeMap μ (σ : Fin n → E) (atl_selRand μ σ f t s A p))
        ∂((ubfTail n t).prod (Vcube n)))
      = ∑ x, g x * μ x := by
    have hcomp : (∫ p, (fun w => g (codeMap μ (σ : Fin n → E) w)) (atl_selRand μ σ f t s A p)
          ∂((ubfTail n t).prod (Vcube n)))
        = ∫ w, g (codeMap μ (σ : Fin n → E) w) ∂(Vcube n) := by
      rw [← hMP.map_eq, integral_map hMP.measurable.aemeasurable
        (measurable_g_codeMap μ σ g).aestronglyMeasurable, hMP.map_eq]
    rw [hcomp, integral_g_codeMap μ hpos hμ1 σ g]
  rw [← hfub, hmean]; rfl

lemma atl_diag_of_MP (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (e : E)
    (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (hMP : atl_TailSelMP μ σ f t s A) :
    (∫ B, fiberDiag μ σ f e s (acp_join t A B) ∂(ubfTail n t))
      = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) := by
  have hgC : ∀ ω, |f ω * Lindeberg.coord e ω| ≤ 1 := by
    intro ω; rw [abs_mul, ← one_mul (1 : ℝ)]
    exact mul_le_mul (hfC _) (GrandCoupling.abs_coord_le_one e _) (abs_nonneg _) (by norm_num)
  exact atl_innerRand_eq_mean μ hpos hμ1 σ (fun ω => f ω * Lindeberg.coord e ω) hgC t s A hMP

/-- The randomized marginal term of `g` at step `t` and stopping value `s`. -/
noncomputable def atl_margRand (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f g : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) : ℝ :=
  ∫ V, g (codeMap μ (σ : Fin n → E)
        (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) s)) ∂(Vcube n)

lemma atl_margRand_meas (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f g : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (atl_margRand μ σ f g t s A) :=
  (atl_jointMeas μ σ f g t s A).stronglyMeasurable.integral_prod_right'.measurable

lemma atl_margRand_le_one (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f g : ConfigSpace E → ℝ) (hgC : ∀ ω, |g ω| ≤ 1) (t s : ℕ)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
    |atl_margRand μ σ f g t s A B| ≤ 1 := by
  unfold atl_margRand
  calc |∫ V, g (codeMap μ (σ : Fin n → E)
          (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) s)) ∂(Vcube n)|
      ≤ ∫ V, |g (codeMap μ (σ : Fin n → E)
          (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) s))| ∂(Vcube n) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ V, (1 : ℝ) ∂(Vcube n) := integral_mono
        (ContinuousFKG.integrable_of_bdd _
          ((measurable_g_codeMap μ σ g).comp ((measurable_adaptWt_fixed _ s).comp
            (measurable_const.prodMk measurable_id))).abs
          (fun V => by rw [abs_abs]; exact hgC _))
        (integrable_const 1) (fun V => hgC _)
    _ = 1 := by simp

lemma atl_marg_of_MP (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (g : ConfigSpace E → ℝ) {Cg : ℝ}
    (hgC : ∀ ω, |g ω| ≤ Cg) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (hMP : atl_TailSelMP μ σ f t s A) :
    (∫ B, atl_margRand μ σ f g t s A B ∂(ubfTail n t)) = Lindeberg.mean μ g :=
  atl_innerRand_eq_mean μ hpos hμ1 σ g hgC t s A hMP

/-- Marginal monotonicity of the randomized marginal term. -/
def atl_MargMonoRand (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f g : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) : Prop :=
  Monotone (atl_margRand μ σ f g t s A)

lemma atl_margMonoRand_of_const {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f g : ConfigSpace E → ℝ}
    (hg : Monotone g) {Cg : ℝ} (hgC : ∀ ω, |g ω| ≤ Cg) (t s : ℕ)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) (m₀ : ℕ)
    (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = m₀) :
    atl_MargMonoRand μ σ f g t s A := by
  have heq : atl_margRand μ σ f g t s A
      = (fun B => ∫ V, g (codeMap μ (σ : Fin n → E)
          (adaptWt (acp_join t A B) V m₀ s)) ∂(Vcube n)) := by
    funext B
    change (∫ V, g (codeMap μ (σ : Fin n → E)
          (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) s)) ∂(Vcube n))
        = ∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m₀ s)) ∂(Vcube n)
    rw [hconst B]
  change Monotone (atl_margRand μ σ f g t s A)
  rw [heq]
  exact atc_marg_mono_B hpos hmono σ hg hgC t m₀ s A

lemma atl_cross_of_MP_mono (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hfC : ∀ ω, |f ω| ≤ 1) (e : E) (t s₁ s₂ : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (hMP1 : atl_TailSelMP μ σ f t s₁ A) (hMP2 : atl_TailSelMP μ σ f t s₂ A)
    (hmono1 : atl_MargMonoRand μ σ f f t s₁ A)
    (hmono2 : atl_MargMonoRand μ σ f (Lindeberg.coord e) t s₂ A) :
    Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
      ≤ ∫ B, fiberCross μ σ f e s₁ s₂ (acp_join t A B) ∂(ubfTail n t) := by
  have hFKG := atc_hasFKG_ubfTail n t (atl_margRand μ σ f f t s₁ A)
    (atl_margRand μ σ f (Lindeberg.coord e) t s₂ A)
    (atl_margRand_meas μ σ f f t s₁ A) (atl_margRand_meas μ σ f (Lindeberg.coord e) t s₂ A)
    ⟨1, fun B => atl_margRand_le_one μ σ f f hfC t s₁ A B⟩
    ⟨1, fun B => atl_margRand_le_one μ σ f (Lindeberg.coord e)
        (fun ω => GrandCoupling.abs_coord_le_one e ω) t s₂ A B⟩
    hmono1 hmono2
  rw [atl_marg_of_MP μ hpos hμ1 σ f hfC t s₁ A hMP1,
      atl_marg_of_MP μ hpos hμ1 σ (Lindeberg.coord e)
        (fun ω => GrandCoupling.abs_coord_le_one e ω) t s₂ A hMP2] at hFKG
  have hcross : (∫ B, fiberCross μ σ f e s₁ s₂ (acp_join t A B) ∂(ubfTail n t))
      = ∫ B, atl_margRand μ σ f f t s₁ A B * atl_margRand μ σ f (Lindeberg.coord e) t s₂ A B
          ∂(ubfTail n t) := rfl
  rw [hcross]; exact hFKG

/-! ## C. The tail law -/

lemma atl_tailCondLaw_of_residues {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hfC : ∀ ω, |f ω| ≤ 1)
    (hMP : ∀ (t : ℕ) (s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ), atl_TailSelMP μ σ f t s A)
    (hMono : ∀ (t s : ℕ) (g : ConfigSpace E → ℝ) (A : {i : Fin n // (i : ℕ) < t} → ℝ),
        atl_MargMonoRand μ σ f g t s A) :
    acp_TailCondLaw μ σ f := by
  intro t htn A
  set e := (σ : Fin n → E) ⟨t, htn⟩ with he
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact atl_diag_of_MP μ hpos hμ1 σ hfC e t t A (hMP t t A)
  · exact atl_diag_of_MP μ hpos hμ1 σ hfC e t (t+1) A (hMP t (t+1) A)
  · exact atl_cross_of_MP_mono μ hpos hμ1 σ hfC e t t (t+1) A (hMP t t A) (hMP t (t+1) A)
      (hMono t t f A) (hMono t (t+1) (Lindeberg.coord e) A)
  · exact atl_cross_of_MP_mono μ hpos hμ1 σ hfC e t (t+1) t A (hMP t (t+1) A) (hMP t t A)
      (hMono t (t+1) f A) (hMono t t (Lindeberg.coord e) A)

lemma atl_fiberDiag_eq_fixed_of_const (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (e : E) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (m₀ : ℕ)
    (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = m₀)
    (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
    fiberDiag μ σ f e s (acp_join t A B) = atc_fiberDiagFixed μ σ f e m₀ s (acp_join t A B) := by
  change atc_fiberDiagFixed μ σ f e (stopVal μ σ f (acp_join t A B)) s (acp_join t A B)
      = atc_fiberDiagFixed μ σ f e m₀ s (acp_join t A B)
  rw [hconst B]

lemma atl_fiberCross_eq_fixed_of_const (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (e : E) (t s₁ s₂ : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (m₀ : ℕ)
    (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = m₀)
    (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
    fiberCross μ σ f e s₁ s₂ (acp_join t A B)
      = atc_fiberCrossFixed μ σ f e m₀ s₁ s₂ (acp_join t A B) := by
  change atc_fiberCrossFixed μ σ f e (stopVal μ σ f (acp_join t A B)) s₁ s₂ (acp_join t A B)
      = atc_fiberCrossFixed μ σ f e m₀ s₁ s₂ (acp_join t A B)
  rw [hconst B]

lemma atl_tailCondLaw_const_switch {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1)
    (atl_const : ∀ (t : ℕ), ({i : Fin n // (i : ℕ) < t} → ℝ) → ℕ)
    (hconst : ∀ (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
        (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ),
        stopVal μ σ f (acp_join t A B) = atl_const t A) :
    acp_TailCondLaw μ σ f := by
  intro t htn A
  set e := (σ : Fin n → E) ⟨t, htn⟩ with he
  set m₀ := atl_const t A with hm₀
  have hc : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = m₀ :=
    fun B => hconst t A B
  have hfix := atc_tailCondLawFixed hpos hμ1 hmono σ hf hfC t htn m₀ A
  obtain ⟨hD1, hD2, hC1, hC2⟩ := hfix
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (∫ B, fiberDiag μ σ f e t (acp_join t A B) ∂(ubfTail n t))
          = ∫ B, atc_fiberDiagFixed μ σ f e m₀ t (acp_join t A B) ∂(ubfTail n t) from by
      apply integral_congr_ae; apply Filter.Eventually.of_forall; intro B
      exact atl_fiberDiag_eq_fixed_of_const μ σ e t t A m₀ hc B]
    exact hD1
  · rw [show (∫ B, fiberDiag μ σ f e (t+1) (acp_join t A B) ∂(ubfTail n t))
          = ∫ B, atc_fiberDiagFixed μ σ f e m₀ (t+1) (acp_join t A B) ∂(ubfTail n t) from by
      apply integral_congr_ae; apply Filter.Eventually.of_forall; intro B
      exact atl_fiberDiag_eq_fixed_of_const μ σ e t (t+1) A m₀ hc B]
    exact hD2
  · rw [show (∫ B, fiberCross μ σ f e t (t+1) (acp_join t A B) ∂(ubfTail n t))
          = ∫ B, atc_fiberCrossFixed μ σ f e m₀ t (t+1) (acp_join t A B) ∂(ubfTail n t) from by
      apply integral_congr_ae; apply Filter.Eventually.of_forall; intro B
      exact atl_fiberCross_eq_fixed_of_const μ σ e t t (t+1) A m₀ hc B]
    exact hC1
  · rw [show (∫ B, fiberCross μ σ f e (t+1) t (acp_join t A B) ∂(ubfTail n t))
          = ∫ B, atc_fiberCrossFixed μ σ f e m₀ (t+1) t (acp_join t A B) ∂(ubfTail n t) from by
      apply integral_congr_ae; apply Filter.Eventually.of_forall; intro B
      exact atl_fiberCross_eq_fixed_of_const μ σ e t (t+1) t A m₀ hc B]
    exact hC2

end AdaptDisintegration

end OSSS

end StatMech
