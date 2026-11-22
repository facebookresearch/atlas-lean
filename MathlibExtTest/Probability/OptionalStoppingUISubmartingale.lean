/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OptionalStoppingUISubmartingale

/-!
# Tests for optional stopping of uniformly integrable submartingales

Restatements of the public signatures in
`MathlibExt.Probability.OptionalStoppingUISubmartingale`, the constant
process as a concrete uniformly integrable submartingale, and a genuinely
strict example: the deterministic increasing process `1 - 2⁻ⁿ`, for which
`∫ f 0 = 0 < 1 - 2⁻⁵ = ∫ f_{τ}` and `∫ f_{τ} < 1 = ∫ f_∞` at the constant
stopping time `τ = 5`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace MathlibExtTest.Probability.OptionalStoppingUISubmartingale

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

/-- Stopping a uniformly integrable submartingale yields a uniformly
integrable stopped process. -/
example (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) :
    UniformIntegrable (stoppedProcess f τ) 1 μ :=
  hsub.uniformIntegrable_stoppedProcess_of_uniformIntegrable hui τ hτ

/-- Optional stopping for uniformly integrable submartingales, restated
with the exact public signature. -/
example (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) :
    (∫ ω, f 0 ω ∂μ ≤ ∫ ω, stoppedValueAtTop f τ ω ∂μ) ∧
    (∫ ω, stoppedValueAtTop f τ ω ∂μ ≤ ∫ ω, ℱ.limitProcess f μ ω ∂μ) :=
  hsub.integral_stoppedValueAtTop_of_uniformIntegrable hui τ hτ

/-- A constant process is a submartingale, uniformly integrable in `L¹`. -/
private theorem uniformIntegrable_const_process (c : ℝ) :
    UniformIntegrable (fun (_ : ℕ) (_ : Ω) => c) 1 μ :=
  uniformIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const c)

/-- The stopped value at a constant finite stopping time is the process
at that time, pointwise. -/
private theorem stoppedValueAtTop_const (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    stoppedValueAtTop f (fun _ => ((k : ℕ) : WithTop ℕ)) ω = f k ω := by
  simp only [stoppedValueAtTop, ite_eq_right (by simp : ¬ ((k : ℕ) : WithTop ℕ) = ⊤)]
  congr 1

/-- For the constant submartingale, the stopped value at the constant
stopping time `5` is the constant itself, pointwise. -/
example (c : ℝ) (ω : Ω) :
    stoppedValueAtTop (fun (_ : ℕ) (_ : Ω) => c) (fun _ => ((5 : ℕ) : WithTop ℕ)) ω = c :=
  stoppedValueAtTop_const _ _ _

/-- For the constant submartingale, stopping at the constant stopping
time `5` preserves the expectation `c`. -/
example (c : ℝ) :
    ∫ ω, stoppedValueAtTop (fun (_ : ℕ) (_ : Ω) => c) (fun _ => ((5 : ℕ) : WithTop ℕ)) ω ∂μ = c := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => stoppedValueAtTop_const _ _ ω)]
  simp [integral_const]

/-- The deterministic increasing process `n ↦ 1 - 2⁻ⁿ` (constant in `ω`)
is a submartingale. -/
private theorem submartingale_one_sub_pow (ℱ : Filtration ℕ m0) :
    Submartingale (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n) ℱ μ := by
  refine submartingale_of_setIntegral_le_succ (fun _ => stronglyMeasurable_const)
    (fun _ => integrable_const _) fun i s _ => ?_
  rw [setIntegral_const, setIntegral_const]
  simp only [smul_eq_mul, Measure.real]
  have hpow : (1 / 2 : ℝ) ^ (i + 1) ≤ (1 / 2 : ℝ) ^ i :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ i)
  have hμ : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 - (1 / 2 : ℝ) ^ i ≤ 1 - (1 / 2 : ℝ) ^ (i + 1)) hμ]

/-- The deterministic increasing process `n ↦ 1 - 2⁻ⁿ` is uniformly
integrable, since it is dominated by the constant `1`. -/
private theorem uniformIntegrable_one_sub_pow :
    UniformIntegrable (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n) 1 μ := by
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ n := fun n => by
    have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  refine ⟨UnifIntegrable.ae_mono (unifIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const 1))
      (fun _ => aestronglyMeasurable_const) (fun n => ?_),
    Real.toNNReal 1, fun n => ?_⟩
  · apply Filter.Eventually.of_forall
    intro ω
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (hnn n), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ))]
    exact ENNReal.ofReal_le_ofReal (sub_le_self 1 (by positivity))
  · rw [eLpNorm_one_eq_lintegral_enorm aestronglyMeasurable_const]
    calc ∫⁻ ω, ‖(1 - (1 / 2 : ℝ) ^ n : ℝ)‖ₑ ∂μ
        ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂μ := by
          refine lintegral_mono_ae ?_
          apply Filter.Eventually.of_forall
          intro ω
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn n)]
          simp
      _ = 1 := by simp
      _ = ((Real.toNNReal 1 : ℝ≥0) : ℝ≥0∞) := by simp

/-- For the deterministic increasing process, the stopped value at the
constant stopping time `5` is `1 - 2⁻⁵`, pointwise. -/
example (ω : Ω) :
    stoppedValueAtTop (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n)
      (fun _ => ((5 : ℕ) : WithTop ℕ)) ω = 1 - (1 / 2 : ℝ) ^ 5 :=
  stoppedValueAtTop_const _ _ _

/-- For the deterministic increasing process, the expectation inequality
is strict on both sides at the constant stopping time `5`:
`∫ f 0 = 0 < 1 - 2⁻⁵ = ∫ f_τ < 1 = ∫ f_∞`. -/
example :
    (0 : ℝ) < 1 - (1 / 2 : ℝ) ^ 5 ∧ 1 - (1 / 2 : ℝ) ^ 5 < 1 := by
  have hsub := submartingale_one_sub_pow (μ := μ) ℱ
  have hui := uniformIntegrable_one_sub_pow (μ := μ)
  have h := hsub.integral_stoppedValueAtTop_of_uniformIntegrable hui
    (fun _ => ((5 : ℕ) : WithTop ℕ)) (isStoppingTime_const ℱ 5)
  have hInt0 : ∫ ω, (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n) 0 ω ∂μ = 0 := by
    simp
  have hIntStop : ∫ ω, stoppedValueAtTop (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n)
      (fun _ => ((5 : ℕ) : WithTop ℕ)) ω ∂μ = 1 - (1 / 2 : ℝ) ^ 5 := by
    have hpt : ∀ ω, stoppedValueAtTop (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n)
        (fun _ => ((5 : ℕ) : WithTop ℕ)) ω = 1 - (1 / 2 : ℝ) ^ 5 :=
      fun ω => stoppedValueAtTop_const _ _ _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    simp [integral_const]
  have hIntLim : ∫ ω, ℱ.limitProcess (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n) μ ω ∂μ = 1 := by
    have hlim : ∀ᵐ ω ∂μ, ℱ.limitProcess (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n) μ ω = 1 := by
      obtain ⟨C, hC⟩ := hui.2
      filter_upwards [hsub.ae_tendsto_limitProcess hC] with ω hω
      refine tendsto_nhds_unique hω ?_
      have hpow : Filter.Tendsto (fun n => (1 / 2 : ℝ) ^ n) Filter.atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa using tendsto_const_nhds.sub hpow
    rw [integral_congr_ae hlim]
    simp [integral_const]
  rw [hInt0, hIntStop, hIntLim] at h
  constructor <;> linarith [h.1, h.2, (by norm_num : (0 : ℝ) < (1 / 2 : ℝ) ^ 5)]

/-- The same process changes with time: its values at `0` and `1` are
`0` and `1 / 2`, so a constant-process fixture cannot cover this case. -/
example (ω : Ω) :
    (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n) 0 ω = 0 ∧
    (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n) 1 ω = 1 / 2 ∧
    (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n) 0 ω <
      (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n) 1 ω := by
  norm_num

/-- The limiting value is proved independently of optional stopping. -/
private theorem tendsto_one_sub_pow :
    Tendsto (fun n : ℕ => 1 - (1 / 2 : ℝ) ^ n) atTop (𝓝 1) := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using tendsto_const_nhds.sub hpow

/-- At the infinite stopping time, `limUnder` gives the actual limit `1`,
rather than the initial value `0`. -/
private theorem stoppedValueAtTop_one_sub_pow_top (ω : Ω) :
    stoppedValueAtTop (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n)
      (fun _ => (⊤ : WithTop ℕ)) ω = 1 := by
  simp only [stoppedValueAtTop, ite_true]
  exact tendsto_one_sub_pow.limUnder_eq

/-- The `τ = ⊤` branch evaluates the nonconstant process to `1` pointwise. -/
example (ω : Ω) :
    stoppedValueAtTop (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n)
      (fun _ => (⊤ : WithTop ℕ)) ω = 1 :=
  stoppedValueAtTop_one_sub_pow_top ω

/-- The expectation at `τ = ⊤` is the independently computed limit `1`. -/
private theorem integral_stoppedValueAtTop_one_sub_pow_top :
    ∫ ω, stoppedValueAtTop (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n)
      (fun _ => (⊤ : WithTop ℕ)) ω ∂μ = 1 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall stoppedValueAtTop_one_sub_pow_top)]
  simp [integral_const]

/-- The integral test exercises the infinite branch with a literal expected value. -/
example :
    ∫ ω, stoppedValueAtTop (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n)
      (fun _ => (⊤ : WithTop ℕ)) ω ∂μ = 1 :=
  integral_stoppedValueAtTop_one_sub_pow_top

/-- Stopping at infinity leaves every finite-time value unchanged. -/
example (n : ℕ) (ω : Ω) :
    stoppedProcess (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n)
      (fun _ => (⊤ : WithTop ℕ)) n ω = 1 - (1 / 2 : ℝ) ^ n := by
  simp only [stoppedProcess, min_top_right]
  rfl

/-- The constant infinite time is a stopping time: every finite sublevel set is empty. -/
private theorem isStoppingTime_top (ℱ : Filtration ℕ m0) :
    IsStoppingTime ℱ (fun _ => (⊤ : WithTop ℕ)) := by
  intro i
  simp

/-- The public preservation theorem applies to this concrete process at infinity. -/
example :
    UniformIntegrable (stoppedProcess (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n)
      (fun _ => (⊤ : WithTop ℕ))) 1 μ :=
  (submartingale_one_sub_pow (μ := μ) ℱ).uniformIntegrable_stoppedProcess_of_uniformIntegrable
    (uniformIntegrable_one_sub_pow (μ := μ)) (fun _ => (⊤ : WithTop ℕ))
    (isStoppingTime_top ℱ)

/-- The public expectation theorem is exercised at infinity; the stopped
expectation is strictly larger than the initial expectation `0`. -/
example :
    (0 : ℝ) < ∫ ω, stoppedValueAtTop (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n)
      (fun _ => (⊤ : WithTop ℕ)) ω ∂μ ∧
    (∫ ω, stoppedValueAtTop (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n)
      (fun _ => (⊤ : WithTop ℕ)) ω ∂μ ≤
        ∫ ω, ℱ.limitProcess (fun (n : ℕ) (_ : Ω) => 1 - (1 / 2 : ℝ) ^ n) μ ω ∂μ) := by
  have h := (submartingale_one_sub_pow (μ := μ) ℱ).integral_stoppedValueAtTop_of_uniformIntegrable
    (uniformIntegrable_one_sub_pow (μ := μ)) (fun _ => (⊤ : WithTop ℕ))
    (isStoppingTime_top ℱ)
  constructor
  · rw [integral_stoppedValueAtTop_one_sub_pow_top]
    norm_num
  · exact h.2

#print axioms Submartingale.uniformIntegrable_stoppedProcess_of_uniformIntegrable
#print axioms Submartingale.integral_stoppedValueAtTop_of_uniformIntegrable

end MathlibExtTest.Probability.OptionalStoppingUISubmartingale
