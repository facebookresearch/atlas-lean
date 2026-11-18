/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Decision.Risk.Countable
public import Mathlib.Probability.Decision.BayesEstimator
public import Mathlib.Probability.Kernel.Basic

/-!
# Weighted-score Bayes rule for finite binary decisions

For densities `P0, P1` on a finite observation space, prior weight `π`,
and costs `cFP, cFN`, the weighted scores at `x` are
`S1 x = (1 - π) * cFP * P0 x` (cost of deciding `true`) and
`S0 x = π * cFN * P1 x` (cost of deciding `false`). No division is formed
anywhere: in particular no likelihood ratio and no posterior odds.

The deterministic rule that decides by the strict weighted-score
comparison is a Bayes estimator, by the existing expected-loss argmin
optimality theorem. A randomized rule following the strict comparisons
minimizes the real risk over every randomized competitor. Randomization
is free exactly at genuine weighted ties
`π * cFN * P1 x = (1 - π) * cFP * P0 x`, which include joint-zero support;
one-sided support strictly favors the supported decision. Equal densities
alone are not a tie under unequal priors or costs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MathlibExt.Probability.Decision

/-- Per-observation real contribution of randomization level `a` at `x`:
`a * S1 x + (1 - a) * S0 x`. -/
def weightedScoreContribution {𝒳 : Type*} (P0 P1 : 𝒳 → ℝ) (π cFP cFN a : ℝ) (x : 𝒳) : ℝ :=
  a * ((1 - π) * cFP * P0 x) + (1 - a) * (π * cFN * P1 x)

private theorem weightedScore_bayesRule_exists_aux
    {𝒳 : Type*} [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [Fintype 𝒳]
    (P0 P1 : 𝒳 → ℝ) (π cFP cFN : ℝ)
    (_hP0 : ∀ x, 0 ≤ P0 x) (_hP0sum : ∑ x, P0 x = 1)
    (_hP1 : ∀ x, 0 ≤ P1 x) (_hP1sum : ∑ x, P1 x = 1)
    (hπ0 : 0 < π) (hπ1 : π < 1) (hcFP : 0 < cFP) (hcFN : 0 < cFN) :
    (∃ f : 𝒳 → Bool, ∃ hf : Measurable f,
      (∀ x, (1 - π) * cFP * P0 x < π * cFN * P1 x → f x = true)
      ∧ (∀ x, π * cFN * P1 x < (1 - π) * cFP * P0 x → f x = false)
      ∧ IsBayesEstimator
          (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
          (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
          (Kernel.deterministic f hf)
          (ENNReal.ofReal (1 - π) • Measure.dirac false
            + ENNReal.ofReal π • Measure.dirac true)) := by
  classical
  refine ⟨fun x => if (1 - π) * cFP * P0 x < π * cFN * P1 x then true else false,
    measurable_of_countable _, ?_, ?_, ?_⟩
  · intro x hx
    simp [hx]
  · intro x hx
    have h : ¬ (1 - π) * cFP * P0 x < π * cFN * P1 x := by linarith
    simp [h]
  · have h1π : 0 ≤ (1 - π) := by linarith
    have hπnn : 0 ≤ π := le_of_lt hπ0
    have h1πpos : 0 < 1 - π := by linarith
    have hπfalse : (ENNReal.ofReal (1 - π) • Measure.dirac false
          + ENNReal.ofReal π • Measure.dirac true) {false}
        = ENNReal.ofReal (1 - π) := by
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
      simp
    have hπtrue : (ENNReal.ofReal (1 - π) • Measure.dirac false
          + ENNReal.ofReal π • Measure.dirac true) {true}
        = ENNReal.ofReal π := by
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
      simp
    have hπfalse_ne : (ENNReal.ofReal (1 - π) • Measure.dirac false
          + ENNReal.ofReal π • Measure.dirac true) {false} ≠ 0 := by
      rw [hπfalse]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr h1πpos)
    have hπtrue_ne : (ENNReal.ofReal (1 - π) • Measure.dirac false
          + ENNReal.ofReal π • Measure.dirac true) {true} ≠ 0 := by
      rw [hπtrue]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr hπ0)
    have hdist : ∀ (c : 𝒳 → ℝ≥0∞) (s : Finset 𝒳) (t : Set 𝒳),
        (∑ z ∈ s, c z • Measure.dirac z) t = ∑ z ∈ s, (c z • Measure.dirac z) t := by
      intro c s t
      induction s using Finset.induction with
      | empty => simp
      | insert a s' ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.add_apply, ih]
    have hμ0x : ∀ x, (∑ z, ENNReal.ofReal (P0 z) • Measure.dirac z) {x}
        = ENNReal.ofReal (P0 x) := by
      intro x
      have h0 : ∀ z ∈ Finset.univ, z ≠ x →
          (ENNReal.ofReal (P0 z) • Measure.dirac z) {x} = 0 := by
        intro z _ hzx
        rw [Measure.smul_apply, smul_eq_mul]
        simp [hzx]
      have hx : x ∉ Finset.univ → (ENNReal.ofReal (P0 x) • Measure.dirac x) {x} = 0 := by
        intro hcon
        simp at hcon
      calc (∑ z, ENNReal.ofReal (P0 z) • Measure.dirac z) {x}
          = ∑ z ∈ Finset.univ, (ENNReal.ofReal (P0 z) • Measure.dirac z) {x} := hdist _ _ _
        _ = (ENNReal.ofReal (P0 x) • Measure.dirac x) {x} :=
            Finset.sum_eq_single (s := Finset.univ)
              (f := fun z => (ENNReal.ofReal (P0 z) • Measure.dirac z) {x}) x h0 hx
        _ = ENNReal.ofReal (P0 x) := by rw [Measure.smul_apply, smul_eq_mul]; simp
    have hμ1x : ∀ x, (∑ z, ENNReal.ofReal (P1 z) • Measure.dirac z) {x}
        = ENNReal.ofReal (P1 x) := by
      intro x
      have h0 : ∀ z ∈ Finset.univ, z ≠ x →
          (ENNReal.ofReal (P1 z) • Measure.dirac z) {x} = 0 := by
        intro z _ hzx
        rw [Measure.smul_apply, smul_eq_mul]
        simp [hzx]
      have hx : x ∉ Finset.univ → (ENNReal.ofReal (P1 x) • Measure.dirac x) {x} = 0 := by
        intro hcon
        simp at hcon
      calc (∑ z, ENNReal.ofReal (P1 z) • Measure.dirac z) {x}
          = ∑ z ∈ Finset.univ, (ENNReal.ofReal (P1 z) • Measure.dirac z) {x} := hdist _ _ _
        _ = (ENNReal.ofReal (P1 x) • Measure.dirac x) {x} :=
            Finset.sum_eq_single (s := Finset.univ)
              (f := fun z => (ENNReal.ofReal (P1 z) • Measure.dirac z) {x}) x h0 hx
        _ = ENNReal.ofReal (P1 x) := by rw [Measure.smul_apply, smul_eq_mul]; simp
    have hfin0 : IsFiniteMeasure (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x) := by
      have h : ∀ s : Finset 𝒳,
          IsFiniteMeasure (∑ z ∈ s, ENNReal.ofReal (P0 z) • Measure.dirac z) := by
        intro s
        induction s using Finset.induction with
        | empty => refine ⟨?_⟩; simp
        | insert a s' ha ih =>
            rw [Finset.sum_insert ha]
            have h1 : IsFiniteMeasure (ENNReal.ofReal (P0 a) • Measure.dirac a) :=
              Measure.smul_finite _ (ne_of_lt ENNReal.ofReal_lt_top)
            exact isFiniteMeasureAdd
      exact h Finset.univ
    have hfin1 : IsFiniteMeasure (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) := by
      have h : ∀ s : Finset 𝒳,
          IsFiniteMeasure (∑ z ∈ s, ENNReal.ofReal (P1 z) • Measure.dirac z) := by
        intro s
        induction s using Finset.induction with
        | empty => refine ⟨?_⟩; simp
        | insert a s' ha ih =>
            rw [Finset.sum_insert ha]
            have h1 : IsFiniteMeasure (ENNReal.ofReal (P1 a) • Measure.dirac a) :=
              Measure.smul_finite _ (ne_of_lt ENNReal.ofReal_lt_top)
            exact isFiniteMeasureAdd
      exact h Finset.univ
    have hfinπ : IsFiniteMeasure (ENNReal.ofReal (1 - π) • Measure.dirac false
        + ENNReal.ofReal π • Measure.dirac true) := by
      have h1 : IsFiniteMeasure (ENNReal.ofReal (1 - π) • Measure.dirac (false : Bool)) :=
        Measure.smul_finite _ (ne_of_lt ENNReal.ofReal_lt_top)
      have h2 : IsFiniteMeasure (ENNReal.ofReal π • Measure.dirac (true : Bool)) :=
        Measure.smul_finite _ (ne_of_lt ENNReal.ofReal_lt_top)
      exact isFiniteMeasureAdd
    have hfinmix : IsFiniteMeasure (Kernel.boolKernel
          (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
          (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
          (ENNReal.ofReal (1 - π) • Measure.dirac false
            + ENNReal.ofReal π • Measure.dirac true)) := by
      refine ⟨?_⟩
      rw [boolKernel_comp_measure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        smul_eq_mul, smul_eq_mul]
      exact (ENNReal.add_lt_top).mpr
        ⟨ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _),
          ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)⟩
    have hPfin : IsFiniteKernel (Kernel.boolKernel
          (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
          (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x)) := inferInstance
    have hLD0 : (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x).HaveLebesgueDecomposition
          (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) :=
      Measure.haveLebesgueDecomposition_of_finiteMeasure
    have hLD1 : (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x).HaveLebesgueDecomposition
          (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) :=
      Measure.haveLebesgueDecomposition_of_finiteMeasure
    have hpostF_ae :=
      posterior_boolKernel_apply_false (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
        (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x)
        (ENNReal.ofReal (1 - π) • Measure.dirac false + ENNReal.ofReal π • Measure.dirac true)
    have hpostT_ae :=
      posterior_boolKernel_apply_true (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
        (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x)
        (ENNReal.ofReal (1 - π) • Measure.dirac false + ENNReal.ofReal π • Measure.dirac true)
    have hmixx : ∀ x, (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) {x}
        = (ENNReal.ofReal (1 - π) • Measure.dirac false
            + ENNReal.ofReal π • Measure.dirac true) {true}
            * (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) {x}
          + (ENNReal.ofReal (1 - π) • Measure.dirac false
            + ENNReal.ofReal π • Measure.dirac true) {false}
            * (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x) {x} := by
      intro x
      rw [boolKernel_comp_measure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        smul_eq_mul, smul_eq_mul]
    have hD0 : ∀ x, ((∑ z, ENNReal.ofReal (P0 z) • Measure.dirac z).rnDeriv
            (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true))) x
          * (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) {x}
        = ENNReal.ofReal (P0 x) := by
      intro x
      have hac : (∑ z, ENNReal.ofReal (P0 z) • Measure.dirac z)
          ≪ (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) :=
        absolutelyContinuous_boolKernel_comp_left
          (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
          (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) hπfalse_ne
      have hset := Measure.setLIntegral_rnDeriv hac {x}
      rw [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
        mul_comm, hμ0x] at hset
      exact hset
    have hD1 : ∀ x, ((∑ z, ENNReal.ofReal (P1 z) • Measure.dirac z).rnDeriv
            (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true))) x
          * (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) {x}
        = ENNReal.ofReal (P1 x) := by
      intro x
      have hac : (∑ z, ENNReal.ofReal (P1 z) • Measure.dirac z)
          ≪ (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) :=
        absolutelyContinuous_boolKernel_comp_right
          (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
          (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) hπtrue_ne
      have hset := Measure.setLIntegral_rnDeriv hac {x}
      rw [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
        mul_comm, hμ1x] at hset
      exact hset
    have hE1 : ∀ x, ∫⁻ θ, (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ true
          ∂((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x)
        = ENNReal.ofReal cFP * ((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x) {false} := by
      intro x
      rw [lintegral_fintype]
      simp only [Fintype.sum_bool]
      simp
    have hE0 : ∀ x, ∫⁻ θ, (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ false
          ∂((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x)
        = ENNReal.ofReal cFN * ((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x) {true} := by
      intro x
      rw [lintegral_fintype]
      simp only [Fintype.sum_bool]
      simp
    have hiInf : ∀ x, (⨅ y, ∫⁻ θ, (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ y
          ∂((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x))
        = (∫⁻ θ, (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ false
          ∂((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x))
          ⊓ (∫⁻ θ, (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ true
          ∂((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x)) := by
      intro x
      apply le_antisymm
      · exact le_inf (iInf_le _ false) (iInf_le _ true)
      · apply le_iInf
        intro y
        cases y
        · exact inf_le_left
        · exact inf_le_right
    have hf1 : ∀ x, (1 - π) * cFP * P0 x < π * cFN * P1 x →
        (fun x => if (1 - π) * cFP * P0 x < π * cFN * P1 x then true else false) x = true := by
      intro x hx
      simp [hx]
    have hf0 : ∀ x, π * cFN * P1 x < (1 - π) * cFP * P0 x →
        (fun x => if (1 - π) * cFP * P0 x < π * cFN * P1 x then true else false) x = false := by
      intro x hx
      have h : ¬ (1 - π) * cFP * P0 x < π * cFN * P1 x := by linarith
      simp [h]
    have hftie : ∀ x, (1 - π) * cFP * P0 x = π * cFN * P1 x →
        (fun x => if (1 - π) * cFP * P0 x < π * cFN * P1 x then true else false) x = false := by
      intro x heq
      have h : ¬ (1 - π) * cFP * P0 x < π * cFN * P1 x := by
        rw [heq]
        exact lt_irrefl _
      simp [h]
    have hprop : ∀ᵐ x ∂(Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)),
          ∫⁻ θ, (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ
            ((fun x => if (1 - π) * cFP * P0 x < π * cFN * P1 x then true else false) x)
          ∂((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x)
        = ⨅ y, ∫⁻ θ, (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ y
          ∂((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x) := by
      rw [ae_iff_of_countable]
      intro x hx0
      have hpostF := ae_iff_of_countable.mp hpostF_ae x hx0
      have hpostT := ae_iff_of_countable.mp hpostT_ae x hx0
      have hMtop : (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) {x} ≠ ⊤ := by
        rw [hmixx]
        exact ne_of_lt ((ENNReal.add_lt_top).mpr
          ⟨ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _),
            ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)⟩)
      have hMpos : 0 < ((Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) {x}).toReal :=
        ENNReal.toReal_pos hx0 hMtop
      have hpostprob : IsProbabilityMeasure ((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x) :=
        IsMarkovKernel.isProbabilityMeasure x
      have hpostF_lt : ((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x) {false} < ⊤ :=
        lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (by
          rw [hpostprob.measure_univ]
          exact ENNReal.one_lt_top)
      have hpostT_lt : ((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x) {true} < ⊤ :=
        lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (by
          rw [hpostprob.measure_univ]
          exact ENNReal.one_lt_top)
      have hE1top : (∫⁻ θ, (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ true
          ∂((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x)) ≠ ⊤ := by
        rw [hE1 x]
        exact ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpostF_lt)
      have hE0top : (∫⁻ θ, (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ false
          ∂((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x)) ≠ ⊤ := by
        rw [hE0 x]
        exact ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpostT_lt)
      have hsc1 : (∫⁻ θ, (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ true
          ∂((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x))
          * (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) {x}
          = ENNReal.ofReal ((1 - π) * cFP * P0 x) := by
        rw [hE1 x, hpostF, hπfalse]
        have d : ENNReal.ofReal ((1 - π) * cFP * P0 x)
            = ENNReal.ofReal (1 - π) * ENNReal.ofReal cFP * ENNReal.ofReal (P0 x) := by
          have h2 : 0 ≤ (1 - π) * cFP := by positivity
          rw [ENNReal.ofReal_mul h2, ENNReal.ofReal_mul h1π]
        rw [d, ← hD0 x]
        ring
      have hsc0 : (∫⁻ θ, (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ false
          ∂((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x))
          * (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) {x}
          = ENNReal.ofReal (π * cFN * P1 x) := by
        rw [hE0 x, hpostT, hπtrue]
        have d : ENNReal.ofReal (π * cFN * P1 x)
            = ENNReal.ofReal π * ENNReal.ofReal cFN * ENNReal.ofReal (P1 x) := by
          have h2 : 0 ≤ π * cFN := by positivity
          rw [ENNReal.ofReal_mul h2, ENNReal.ofReal_mul hπnn]
        rw [d, ← hD1 x]
        ring
      have hS1nn : 0 ≤ (1 - π) * cFP * P0 x :=
        mul_nonneg (mul_nonneg h1π (le_of_lt hcFP)) (_hP0 x)
      have hS0nn : 0 ≤ π * cFN * P1 x :=
        mul_nonneg (mul_nonneg hπnn (le_of_lt hcFN)) (_hP1 x)
      have e1 : (∫⁻ θ, (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ true
          ∂((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x)).toReal
          * ((Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) {x}).toReal
          = (1 - π) * cFP * P0 x := by
        have hcon := congrArg ENNReal.toReal hsc1
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hS1nn] at hcon
        exact hcon
      have e0 : (∫⁻ θ, (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ false
          ∂((posterior (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) x)).toReal
          * ((Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
            (ENNReal.ofReal (1 - π) • Measure.dirac false
              + ENNReal.ofReal π • Measure.dirac true)) {x}).toReal
          = π * cFN * P1 x := by
        have hcon := congrArg ENNReal.toReal hsc0
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hS0nn] at hcon
        exact hcon
      rcases lt_trichotomy ((1 - π) * cFP * P0 x) (π * cFN * P1 x) with hlt | heq | hgt
      · have hfx : (fun x => if (1 - π) * cFP * P0 x < π * cFN * P1 x then true else false) x
            = true := hf1 x hlt
        rw [hfx, hiInf x]
        have hrr : (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ true
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)).toReal
            * ((Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) {x}).toReal
            ≤ (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ false
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)).toReal
            * ((Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) {x}).toReal := by
          rw [e1, e0]
          exact le_of_lt hlt
        have hle_r : (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ true
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)).toReal
            ≤ (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ false
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)).toReal :=
          le_of_mul_le_mul_right hrr hMpos
        have hle : (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ true
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x))
            ≤ (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ false
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)) :=
          (ENNReal.toReal_le_toReal hE1top hE0top).mp hle_r
        exact (inf_eq_right.mpr hle).symm
      · have hfx : (fun x => if (1 - π) * cFP * P0 x < π * cFN * P1 x then true else false) x
            = false := hftie x heq
        rw [hfx, hiInf x]
        refine (inf_eq_left.mpr ?_).symm
        have e0' : (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ false
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)).toReal
            * ((Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) {x}).toReal
            = (1 - π) * cFP * P0 x := by
          rw [e0]
          exact heq.symm
        have heqmul : (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ false
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)).toReal
            * ((Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) {x}).toReal
            = (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ true
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)).toReal
            * ((Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) {x}).toReal :=
          e0'.trans e1.symm
        have hteq : (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ false
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)).toReal
            = (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ true
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)).toReal :=
          mul_right_cancel₀ (ne_of_gt hMpos) heqmul
        exact (ENNReal.toReal_le_toReal hE0top hE1top).mp (le_of_eq hteq)
      · have hfx : (fun x => if (1 - π) * cFP * P0 x < π * cFN * P1 x then true else false) x
            = false := hf0 x hgt
        rw [hfx, hiInf x]
        refine (inf_eq_left.mpr ?_).symm
        have hrr : (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ false
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)).toReal
            * ((Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) {x}).toReal
            ≤ (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ true
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)).toReal
            * ((Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) ∘ₘ
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) {x}).toReal := by
          rw [e0, e1]
          exact le_of_lt hgt
        have hle_r : (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ false
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)).toReal
            ≤ (∫⁻ θ, (fun θ y => if θ = y then 0
              else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) θ true
            ∂((posterior (Kernel.boolKernel
              (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
              (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
              (ENNReal.ofReal (1 - π) • Measure.dirac false
                + ENNReal.ofReal π • Measure.dirac true)) x)).toReal :=
          le_of_mul_le_mul_right hrr hMpos
        exact (ENNReal.toReal_le_toReal hE0top hE1top).mp hle_r
    have hmeas : Measurable
        (fun x => if (1 - π) * cFP * P0 x < π * cFN * P1 x then true else false) :=
      measurable_of_countable _
    have hl : Measurable (Function.uncurry (fun θ y => if θ = y then 0
        else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN)) :=
      measurable_of_countable _
    have harg : IsArgminEstimator
        (fun θ y => if θ = y then 0
          else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
        (Kernel.boolKernel
          (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
          (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
        (ENNReal.ofReal (1 - π) • Measure.dirac false
          + ENNReal.ofReal π • Measure.dirac true)
        (fun x => if (1 - π) * cFP * P0 x < π * cFN * P1 x then true else false) :=
      IsArgminEstimator.mk hmeas hprop
    exact IsArgminEstimator.isBayesEstimator harg hl

/-- Production statement.

Weighted-score Bayes rule for the finite unequal-cost binary model of
copied expression (copied expression of its loss, experiment kernel and prior below).

For every randomized rule `δ`, the displayed deterministic weighted-score
rule is optimal among ALL randomized rules, and it is a Bayes estimator in
Mathlib's sense (`IsBayesEstimator`, via the existing
`IsArgminEstimator.isBayesEstimator` optimality in the proof). The tie and
zero-support clauses characterize exactly when randomization is free:
genuine weighted ties `π * cFN * P1 x = (1 - π) * cFP * P0 x`, one-sided
support `P0 x = 0 < P1 x` (score strictly favors `true`, no division), and
joint-zero support `P0 x = P1 x = 0` (both scores `0`, free randomization,
zero contribution). -/
theorem weightedScore_binary_optimal
    {𝒳 : Type*} [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [Fintype 𝒳]
    (P0 P1 : 𝒳 → ℝ) (π cFP cFN : ℝ)
    (hP0 : ∀ x, 0 ≤ P0 x) (hP0sum : ∑ x, P0 x = 1)
    (hP1 : ∀ x, 0 ≤ P1 x) (hP1sum : ∑ x, P1 x = 1)
    (hπ0 : 0 < π) (hπ1 : π < 1) (hcFP : 0 < cFP) (hcFN : 0 < cFN) :
    -- (i) A measurable deterministic weighted-score rule exists and is a
    -- Bayes estimator; this is the instantiation of the existing
    -- expected-loss argmin optimality (`IsArgminEstimator.isBayesEstimator`).
    (∃ f : 𝒳 → Bool, ∃ hf : Measurable f,
      (∀ x, (1 - π) * cFP * P0 x < π * cFN * P1 x → f x = true)
      ∧ (∀ x, π * cFN * P1 x < (1 - π) * cFP * P0 x → f x = false)
      ∧ IsBayesEstimator
          -- copied expression (copied expression loss/kernel/prior):
          (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
          (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
          (Kernel.deterministic f hf)
          (ENNReal.ofReal (1 - π) • Measure.dirac false
            + ENNReal.ofReal π • Measure.dirac true))
    -- (ii) Optimality among all randomized rules: any rule following the
    -- strict weighted-score comparisons minimizes the real risk over every
    -- randomized competitor δ.
    ∧ (∀ δ δ' : 𝒳 → ℝ, (∀ x, δ x ∈ Set.Icc (0 : ℝ) 1) → (∀ x, δ' x ∈ Set.Icc (0 : ℝ) 1)
        → (∀ x, (1 - π) * cFP * P0 x < π * cFN * P1 x → δ' x = 1)
        → (∀ x, π * cFN * P1 x < (1 - π) * cFP * P0 x → δ' x = 0)
        → (1 - π) * cFP * (∑ x, P0 x * δ' x) + π * cFN * (∑ x, P1 x * (1 - δ' x))
          ≤ (1 - π) * cFP * (∑ x, P0 x * δ x) + π * cFN * (∑ x, P1 x * (1 - δ x)))
    -- (iii) Genuine tie: at a weighted tie the per-observation contribution
    -- is the same for every randomization level, so arbitrary randomization
    -- there does not change the risk.
    ∧ (∀ x : 𝒳, π * cFN * P1 x = (1 - π) * cFP * P0 x
        → ∀ a b : ℝ, weightedScoreContribution P0 P1 π cFP cFN a x = weightedScoreContribution P0 P1 π cFP cFN b x)
    -- (iv) One-sided support: P0 x = 0 < P1 x strictly favors `true`
    -- (stated as a score inequality; no ratio is formed).
    ∧ (∀ x : 𝒳, P0 x = 0 → 0 < P1 x
        → (1 - π) * cFP * P0 x < π * cFN * P1 x)
    -- (v) Joint-zero support: both weighted scores are 0, the contribution
    -- is 0 for every randomization level, and the point is a genuine tie.
    ∧ (∀ x : 𝒳, P0 x = 0 → P1 x = 0
        → π * cFN * P1 x = (1 - π) * cFP * P0 x
          ∧ ∀ a : ℝ, weightedScoreContribution P0 P1 π cFP cFN a x = 0) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact weightedScore_bayesRule_exists_aux P0 P1 π cFP cFN hP0 hP0sum hP1 hP1sum hπ0 hπ1 hcFP hcFN
  · intro δ δ' hδ hδ' h1 h0
    have hEq : ∀ η : 𝒳 → ℝ, (1 - π) * cFP * (∑ x, P0 x * η x) + π * cFN * (∑ x, P1 x * (1 - η x))
        = ∑ x, weightedScoreContribution P0 P1 π cFP cFN (η x) x := by
      intro η
      unfold weightedScoreContribution
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hEq δ', hEq δ]
    apply Finset.sum_le_sum
    intro x _
    have hxδ : 0 ≤ δ x ∧ δ x ≤ 1 := Set.mem_Icc.mp (hδ x)
    have hxδ' : 0 ≤ δ' x ∧ δ' x ≤ 1 := Set.mem_Icc.mp (hδ' x)
    rcases lt_trichotomy ((1 - π) * cFP * P0 x) (π * cFN * P1 x) with hlt | heq | hgt
    · have hd : δ' x = 1 := h1 x hlt
      unfold weightedScoreContribution
      rw [hd]
      have h1δ : 0 ≤ 1 - δ x := by linarith [hxδ.2]
      have hS : 0 < π * cFN * P1 x - (1 - π) * cFP * P0 x := by linarith
      have hnn : 0 ≤ (1 - δ x) * (π * cFN * P1 x - (1 - π) * cFP * P0 x) :=
        mul_nonneg h1δ (le_of_lt hS)
      linarith [hnn]
    · unfold weightedScoreContribution
      rw [heq]
      have e1 : δ' x * (π * cFN * P1 x) + (1 - δ' x) * (π * cFN * P1 x) = π * cFN * P1 x := by ring
      have e2 : δ x * (π * cFN * P1 x) + (1 - δ x) * (π * cFN * P1 x) = π * cFN * P1 x := by ring
      rw [e1, e2]
    · have hd : δ' x = 0 := h0 x hgt
      unfold weightedScoreContribution
      rw [hd]
      have hS : 0 < (1 - π) * cFP * P0 x - π * cFN * P1 x := by linarith
      have hnn : 0 ≤ δ x * ((1 - π) * cFP * P0 x - π * cFN * P1 x) :=
        mul_nonneg hxδ.1 (le_of_lt hS)
      linarith [hnn]
  · intro x hx a b
    unfold weightedScoreContribution
    rw [hx]
    ring
  · intro x hx0 hx1
    rw [hx0, mul_zero]
    have h2 : 0 < π * cFN * P1 x := by positivity
    exact h2
  · intro x hx0 hx1
    constructor
    · rw [hx0, hx1, mul_zero, mul_zero]
    · intro a
      unfold weightedScoreContribution
      rw [hx0, hx1, mul_zero, mul_zero, mul_zero, mul_zero, add_zero]


theorem weightedScoreContribution_constant_iff {𝒳 : Type*} (P0 P1 : 𝒳 → ℝ)
    (π cFP cFN : ℝ) (x : 𝒳) :
    (∀ a b : ℝ, weightedScoreContribution P0 P1 π cFP cFN a x
      = weightedScoreContribution P0 P1 π cFP cFN b x)
      ↔ π * cFN * P1 x = (1 - π) * cFP * P0 x := by
  constructor
  · intro h
    have h10 := h 1 0
    simp only [weightedScoreContribution] at h10
    linarith
  · intro h a b
    simp only [weightedScoreContribution, h]
    ring
end MathlibExt.Probability.Decision
