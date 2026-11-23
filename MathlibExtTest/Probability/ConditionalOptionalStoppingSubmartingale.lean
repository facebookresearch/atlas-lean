/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConditionalOptionalStoppingSubmartingale

@[expose] public section

open MeasureTheory Filter
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

omit [MeasurableSpace Ω] in
/-- The stopped value of a constant process is the constant, at any
stopping time. -/
private lemma stoppedValueAtTop_const (c : ℝ) (τ : Ω → WithTop ℕ) :
    stoppedValueAtTop (fun _ => fun _ => c) τ = fun _ => c := by
  funext ω
  show (if τ ω = ⊤ then limUnder atTop (fun n => (fun _ => fun _ => c) n ω)
    else stoppedValue (fun _ => fun _ => c) τ ω) = c
  by_cases h : τ ω = ⊤
  · rw [ite_eq_left h]
    simpa using (tendsto_const_nhds (x := c)).limUnder_eq
  · rw [ite_eq_right h]
    rfl

/-- The constant process is a uniformly integrable submartingale, so the
main theorem applies to it. -/
private theorem submartingale_const (c : ℝ) :
    Submartingale (fun _ => fun _ => c) ℱ μ :=
  (martingale_const ℱ μ c).submartingale

/-- The constant process is uniformly integrable. -/
private theorem uniformIntegrable_const' (c : ℝ) :
    UniformIntegrable (fun _ : ℕ => fun _ : Ω => c) 1 μ :=
  uniformIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const c)

/-- For the constant process, the conditional optional stopping
inequality says `c ≤ᵐ μ[c | ℱ_L]`, and both sides are `c`. -/
example (c : ℝ) (L M : Ω → WithTop ℕ) (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    (fun _ : Ω => c) ≤ᵐ[μ] μ[fun _ : Ω => c | hL.measurableSpace] := by
  have h := Submartingale.stoppedValueAtTop_le_condExp_stoppedValueAtTop
    (submartingale_const (μ := μ) (ℱ := ℱ) c)
    (uniformIntegrable_const' (μ := μ) c) hL hM hLM
  rw [stoppedValueAtTop_const, stoppedValueAtTop_const] at h
  rw [condExp_const hL.measurableSpace_le] at h ⊢

/-- For the constant process, the expectation form says `∫ c ≤ ∫ c`. -/
example (c : ℝ) (L M : Ω → WithTop ℕ) (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    ∫ ω, stoppedValueAtTop (fun _ => fun _ => c) L ω ∂μ ≤
      ∫ ω, stoppedValueAtTop (fun _ => fun _ => c) M ω ∂μ :=
  Submartingale.integral_stoppedValueAtTop_mono_of_uniformIntegrable
    (submartingale_const (μ := μ) (ℱ := ℱ) c)
    (uniformIntegrable_const' (μ := μ) c) hL hM hLM

/-- Applying the main theorem under abstract hypotheses: this checks the
statement is usable in the form in which it is stated, without
re-proving it. -/
example {f : ℕ → Ω → ℝ}
    (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    stoppedValueAtTop f L ≤ᵐ[μ] μ[stoppedValueAtTop f M | hL.measurableSpace] :=
  Submartingale.stoppedValueAtTop_le_condExp_stoppedValueAtTop hsub hui hL hM hLM

/-- Applying the expectation corollary under abstract hypotheses. -/
example {f : ℕ → Ω → ℝ}
    (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    ∫ ω, stoppedValueAtTop f L ω ∂μ ≤ ∫ ω, stoppedValueAtTop f M ω ∂μ :=
  Submartingale.integral_stoppedValueAtTop_mono_of_uniformIntegrable hsub hui hL hM hLM

#print axioms Submartingale.stoppedValueAtTop_le_condExp_stoppedValueAtTop
#print axioms Submartingale.integral_stoppedValueAtTop_mono_of_uniformIntegrable

omit [MeasurableSpace Ω] in
/-- Finite zero stopping retains the original initial value. -/
theorem characterization_stopped_zero (f : ℕ → Ω → ℝ) :
    stoppedValueAtTop f (fun _ => (0 : WithTop ℕ)) = f 0 := rfl

omit [MeasurableSpace Ω] in
/-- Finite one stopping retains the value after one step. -/
theorem characterization_stopped_one (f : ℕ → Ω → ℝ) :
    stoppedValueAtTop f (fun _ => (1 : WithTop ℕ)) = f 1 := rfl

omit [MeasurableSpace Ω] in
/-- The infinite branch of a signed nonzero constant process is that constant. -/
theorem characterization_negative_constant_infinity :
    stoppedValueAtTop (fun _ : ℕ => fun _ : Ω => (-3 : ℝ)) (fun _ => ⊤) =
      fun _ => (-3 : ℝ) :=
  stoppedValueAtTop_const (-3) _

/-- A bounded deterministic process with a genuine strict increase. -/
def boundedStep (n : ℕ) (_ : Ω) : ℝ := if n = 0 then -2 else 1

theorem boundedStep_submartingale : Submartingale boundedStep ℱ μ := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact stronglyMeasurable_const
  · intro i j hij
    change (fun _ : Ω => if i = 0 then (-2 : ℝ) else 1) ≤ᵐ[μ]
      μ[fun _ : Ω => if j = 0 then (-2 : ℝ) else 1 | ℱ i]
    rw [condExp_const (ℱ.le i)]
    filter_upwards with ω
    by_cases hj : j = 0
    · have hi : i = 0 := Nat.eq_zero_of_le_zero (hj ▸ hij)
      simp [hi, hj]
    · by_cases hi : i = 0 <;> norm_num [hi, hj]
  · intro n
    exact integrable_const _

theorem boundedStep_uniformIntegrable : UniformIntegrable (boundedStep : ℕ → Ω → ℝ) 1 μ := by
  let g : Bool → Ω → ℝ := fun b _ => if b then -2 else 1
  have hfinite : UniformIntegrable g 1 μ :=
    uniformIntegrable_finite le_rfl ENNReal.one_ne_top (fun _ => memLp_const _)
  have heq : (fun n : ℕ => g (decide (n = 0))) = boundedStep := by
    funext n ω
    simp [g, boundedStep]
  rw [← heq]
  obtain ⟨hunif, C, hC⟩ := hfinite
  exact ⟨hunif.comp (fun n : ℕ => decide (n = 0)), C, fun n => hC _⟩

omit [MeasurableSpace Ω] in
/-- The bounded strict process converges to one in the infinite branch. -/
theorem characterization_boundedStep_infinity :
    stoppedValueAtTop (boundedStep : ℕ → Ω → ℝ) (fun _ => ⊤) = fun _ => (1 : ℝ) := by
  funext ω
  change limUnder atTop (fun n => boundedStep n ω) = 1
  have ht : Tendsto (fun n => boundedStep n ω) atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simp [boundedStep, Nat.ne_zero_of_lt hn]
  exact ht.limUnder_eq

/-- The strict submartingale has literal expectations minus two and one. -/
theorem characterization_strict_integrals :
    (∫ ω, stoppedValueAtTop (boundedStep : ℕ → Ω → ℝ) (fun _ => (0 : WithTop ℕ)) ω ∂μ) = -2 ∧
    (∫ ω, stoppedValueAtTop (boundedStep : ℕ → Ω → ℝ) (fun _ => (1 : WithTop ℕ)) ω ∂μ) = 1 := by
  norm_num [stoppedValueAtTop, stoppedValue, boundedStep]

/-- The original conditional theorem applies to a nonmartingale process across zero and one. -/
theorem characterization_strict_conditional :
    stoppedValueAtTop (boundedStep : ℕ → Ω → ℝ) (fun _ => (0 : WithTop ℕ)) ≤ᵐ[μ]
      μ[stoppedValueAtTop boundedStep (fun _ => (1 : WithTop ℕ)) |
        (isStoppingTime_const ℱ (0 : ℕ)).measurableSpace] :=
  Submartingale.stoppedValueAtTop_le_condExp_stoppedValueAtTop boundedStep_submartingale
    boundedStep_uniformIntegrable (isStoppingTime_const ℱ _) (isStoppingTime_const ℱ _)
    (fun _ => by norm_num)
