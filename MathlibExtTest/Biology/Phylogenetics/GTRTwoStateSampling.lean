/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.GTRTwoStateSampling

/-!
# Tests for the i.i.d. GTR sampling instance

* A concrete two-state GTR model (`π = (1/4, 3/4)`, exchangeability `2`): its rate matrix and
  trace computed from `gtrRate`, the parameter hypotheses checked from the definitions, an
  explicit divergence weight that is positive for `t > 0` (computed from the closed form, not
  through `divergenceWeight_pos`), the four sampling hypotheses of T158, and the consistency
  theorem instantiated with its explicit limit `!![-3/4, 3/4; 1/4, -1/4]` and log-det limit `2t`.
* Boundary `t = 0`: the divergence law puts no mass off the diagonal (computed from
  `ctmcTransition_zero`), so it has no full support; the estimator at the exact divergence
  matrix is `0`, not the consistency limit, and no consistency is claimed.
* A non-i.i.d. sample: the constant sequence `X n = site 0` has the right marginal law but is not
  pairwise independent (shown from the explicit weight), so consistency is not claimed for it.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory Filter Topology MeasureTheory

namespace MathlibExtTest.Biology.Phylogenetics.GTRTwoStateSampling

open MathlibExt.Biology.Phylogenetics.GTRTwoStateSampling
open MathlibExt.Biology.Phylogenetics.GTRLogDetRecovery
open MathlibExt.Biology.Phylogenetics.SubstitutionModels

/-! ## A concrete two-state GTR model -/

/-- Base frequencies `(1/4, 3/4)`. -/
noncomputable def π₂ : Fin 2 → ℝ := ![1 / 4, 3 / 4]

/-- Exchangeability `2`. -/
def s₂ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun _ _ => 2

theorem π₂_pos : ∀ i, 0 < π₂ i := by
  intro i; fin_cases i <;> norm_num [π₂]

theorem sum_π₂ : ∑ i, π₂ i = 1 := by
  norm_num [π₂, Fin.sum_univ_two]

theorem s₂_symm : ∀ i j, s₂ i j = s₂ j i := fun _ _ => rfl

theorem s₂_pos : ∀ i j, i ≠ j → 0 < s₂ i j := fun _ _ _ => by norm_num [s₂]

/-- The rate matrix, computed from `gtrRate`. -/
theorem gtrRate_two : gtrRate π₂ s₂ = !![-3 / 2, 3 / 2; 1 / 2, -1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [gtrRate, π₂, s₂]

theorem trace_gtrRate_two : (gtrRate π₂ s₂).trace = -2 := by
  rw [gtrRate_two]
  norm_num [trace, Fin.sum_univ_two]

/-- The parameter hypotheses, checked from the definitions, for every `t ≥ 0`. -/
theorem isSamplingParams_two {t : ℝ} (ht : 0 ≤ t) : IsSamplingParams π₂ s₂ t :=
  ⟨fun i => (π₂_pos i).le, sum_π₂, fun i j h => (s₂_pos i j h).le, ht⟩

/-- The divergence weight of the pair `(0, 1)` is `3/16 * (1 - e^{-2t})`. -/
theorem divergenceWeight_two_01 (t : ℝ) :
    divergenceWeight π₂ s₂ t (0, 1) = 3 / 16 * (1 - Real.exp (-(2 * t))) := by
  rw [divergenceWeight_two sum_π₂ s₂_symm]
  norm_num [π₂, s₂]
  ring

/-- For `t > 0` the off-diagonal pair has positive weight, read off the explicit formula. -/
example {t : ℝ} (ht : 0 < t) : 0 < divergenceWeight π₂ s₂ t (0, 1) := by
  rw [divergenceWeight_two_01]
  have : Real.exp (-(2 * t)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  nlinarith

/-- The point mass of the divergence law at `(0, 1)`. -/
example (t : ℝ) :
    divergenceLaw π₂ s₂ t {(0, 1)} = ENNReal.ofReal (3 / 16 * (1 - Real.exp (-(2 * t)))) := by
  rw [divergenceLaw_singleton, divergenceWeight_two_01]

/-- **The four sampling hypotheses of T158 hold on the two-state model.** -/
example {t : ℝ} (ht : 0 ≤ t) :
    IsProbabilityMeasure (sampleLaw π₂ s₂ t) ∧ (∀ n, Measurable (site (ι := Fin 2) n)) ∧
      (Pairwise fun m n => IndepFun (site m) (site n) (sampleLaw π₂ s₂ t)) ∧
      (∀ n, IdentDistrib (site n) (site 0) (sampleLaw π₂ s₂ t) (sampleLaw π₂ s₂ t)) ∧
      ∀ a : Fin 2 × Fin 2, (sampleLaw π₂ s₂ t).real (site 0 ⁻¹' {a}) =
        π₂ a.1 * ctmcTransition (gtrRate π₂ s₂) t a.1 a.2 :=
  ⟨isProbabilityMeasure_sampleLaw (isSamplingParams_two ht), measurable_site,
    pairwise_indepFun_site (isSamplingParams_two ht), identDistrib_site (isSamplingParams_two ht),
    measureReal_site_preimage_singleton (isSamplingParams_two ht) 0⟩

/-- **Consistency on the two-state model**: almost surely the log-det rate estimate of the
empirical divergence matrix converges to `Q / 2 = !![-3/4, 3/4; 1/4, -1/4]` and the log-det
distance to `2 t`. -/
example {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂sampleLaw π₂ s₂ t,
      Tendsto (fun n => rateEstimate (empiricalDivergence site n ω)) atTop
          (𝓝 !![-3 / 4, 3 / 4; 1 / 4, -1 / 4]) ∧
        Tendsto (fun n => logDetDistance (empiricalDivergence site n ω)) atTop (𝓝 (2 * t)) := by
  have hlim : (-(gtrRate π₂ s₂).trace)⁻¹ • gtrRate π₂ s₂ = !![-3 / 4, 3 / 4; 1 / 4, -1 / 4] := by
    rw [trace_gtrRate_two, gtrRate_two]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hd : -t * (gtrRate π₂ s₂).trace = 2 * t := by
    rw [trace_gtrRate_two]
    ring
  have h := ae_tendsto_rateEstimate_sampleLaw_two π₂_pos sum_π₂ s₂_symm (by norm_num [s₂]) ht
  rw [hlim, hd] at h
  exact h

/-- The in-probability form, at the entry `(0, 1)`: the estimate converges to `3/4`. -/
example {t : ℝ} (ht : 0 < t) :
    TendstoInMeasure (sampleLaw π₂ s₂ t)
      (fun n ω => rateEstimate (empiricalDivergence site n ω) 0 1) atTop fun _ => 3 / 4 := by
  have h := (tendstoInMeasure_rateEstimate_sampleLaw π₂_pos sum_π₂ s₂_symm s₂_pos ht).1 0 1
  have hlim : ((-(gtrRate π₂ s₂).trace)⁻¹ • gtrRate π₂ s₂) 0 1 = 3 / 4 := by
    rw [trace_gtrRate_two, gtrRate_two]
    norm_num
  rw [hlim] at h
  exact h

/-! ## Boundary: `t = 0` -/

/-- At `t = 0` the divergence law puts no mass on the off-diagonal pair `(0, 1)`: no
substitutions, so the law does not have full support. Computed from `ctmcTransition_zero`. -/
theorem divergenceWeight_zero_01 : divergenceWeight π₂ s₂ 0 (0, 1) = 0 := by
  simp [divergenceWeight]

example : divergenceLaw π₂ s₂ 0 {(0, 1)} = 0 := by
  rw [divergenceLaw_singleton, divergenceWeight_zero_01, ENNReal.ofReal_zero]

/-- The full-support conclusion fails at `t = 0`. -/
example : ¬ ∀ a, 0 < divergenceWeight π₂ s₂ 0 a := fun h => by
  have := h (0, 1)
  rw [divergenceWeight_zero_01] at this
  exact lt_irrefl _ this

/-- At `t = 0` the exact divergence matrix is `diagonal π₂`, whose log-det distance is `0` and
whose rate estimate is the zero matrix (computed from `rateEstimate`, Lean's `0⁻¹ = 0`), not the
consistency limit `Q / 2`. The consistency theorems need `0 < t` and are not claimed here, even
though the sampling hypotheses (`isSamplingParams_two le_rfl`) still hold. -/
example : rateEstimate (diagonal π₂ * ctmcTransition (gtrRate π₂ s₂) 0) = 0 ∧
    (-(gtrRate π₂ s₂).trace)⁻¹ • gtrRate π₂ s₂ ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [rateEstimate, logDetDistance_gtr π₂_pos s₂_symm fun i j h => (s₂_pos i j h).le, neg_zero,
      zero_mul, _root_.inv_zero, zero_smul]
  · rw [trace_gtrRate_two, gtrRate_two]
    intro h
    have := congrFun (congrFun h 0) 1
    norm_num at this

/-! ## A non-i.i.d. sample -/

/-- The constant sample: every site pair is a copy of the first. -/
def constSample (_n : ℕ) : (ℕ → Fin 2 × Fin 2) → Fin 2 × Fin 2 := site 0

/-- It is identically distributed with the right marginal law ... -/
example {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IdentDistrib (constSample n) (constSample 0) (sampleLaw π₂ s₂ t) (sampleLaw π₂ s₂ t) ∧
      ∀ a, (sampleLaw π₂ s₂ t).real (constSample 0 ⁻¹' {a}) = divergenceWeight π₂ s₂ t a :=
  ⟨IdentDistrib.refl (measurable_site 0).aemeasurable,
    measureReal_site_preimage_singleton (isSamplingParams_two ht) 0⟩

/-- ... but, for `t > 0`, not pairwise independent: independence of `site 0` with itself would
force the weight `3/16 * (1 - e^{-2t})` of `(0, 1)` to equal its square, while it lies in
`(0, 1)`. So the consistency theorems are not claimed for this sample. -/
example {t : ℝ} (ht : 0 < t) :
    ¬ Pairwise fun m n => IndepFun (constSample m) (constSample n) (sampleLaw π₂ s₂ t) := by
  intro h
  have hp := isSamplingParams_two ht.le
  have := isProbabilityMeasure_sampleLaw hp
  have hmul := (h (show (0 : ℕ) ≠ 1 by decide)).measure_inter_preimage_eq_mul
    {((0 : Fin 2), (1 : Fin 2))} {(0, 1)} (measurableSet_singleton _) (measurableSet_singleton _)
  simp only [constSample, Set.inter_self] at hmul
  have hreal := congrArg ENNReal.toReal hmul
  rw [ENNReal.toReal_mul, ← measureReal_def, measureReal_site_preimage_singleton hp,
    divergenceWeight_two_01] at hreal
  have he : Real.exp (-(2 * t)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have he0 := Real.exp_pos (-(2 * t))
  nlinarith

/-- The general form: with full support, `site 0` is never independent of itself. -/
example {t : ℝ} (ht : 0 < t) : ¬ IndepFun (site 0) (site 0) (sampleLaw π₂ s₂ t) :=
  not_indepFun_site_self π₂_pos sum_π₂ s₂_pos ht

end MathlibExtTest.Biology.Phylogenetics.GTRTwoStateSampling
