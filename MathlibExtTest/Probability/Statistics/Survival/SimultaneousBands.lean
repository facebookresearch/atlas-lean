/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.SimultaneousBands
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open MathlibExt.Probability.Statistics.SimultaneousBands

namespace MathlibExtTest.Probability.Statistics.SimultaneousBands

/-! ### Smoke test: a two-point grid, `n = 4`, so the half-width is `c · w i / 2` -/

/-- Estimate `(1, 2)` on the grid `Fin 2`. -/
noncomputable def est₀ : Fin 2 → ℝ := ![1, 2]

/-- Unit weights. -/
noncomputable def w₀ : Fin 2 → ℝ := ![1, 1]

private theorem sqrt_four : √((4 : ℕ) : ℝ) = 2 := by
  rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Inside the band, computed from the definition: `|1 - 1.25| ≤ 1/2` and `|2 - 2.4| ≤ 1/2`. -/
example : (![1.25, 2.4] : Fin 2 → ℝ) ∈ simultaneousBand est₀ w₀ 1 4 := by
  intro i
  rw [sqrt_four]
  fin_cases i <;> norm_num [est₀, w₀, abs_le]

/-- **Simultaneous strictly stronger than pointwise on a concrete curve.** The curve `(1.25, 3)`
is inside the pointwise interval at grid point `0` but outside the simultaneous band. -/
example : (1.25 : ℝ) ∈ pointwiseInterval est₀ w₀ 1 4 0 ∧
    (![1.25, 3] : Fin 2 → ℝ) ∉ simultaneousBand est₀ w₀ 1 4 := by
  refine ⟨?_, fun h => ?_⟩
  · simp only [pointwiseInterval, mem_ofPred_eq, sqrt_four]
    norm_num [est₀, w₀, abs_le]
  · have h1 := h 1
    rw [sqrt_four] at h1
    norm_num [est₀, w₀, abs_le] at h1

/-- Boundary: a curve exactly on the edge of the band is covered (closed band). -/
example : (![1.5, 1.5] : Fin 2 → ℝ) ∈ simultaneousBand est₀ w₀ 1 4 := by
  intro i
  rw [sqrt_four]
  fin_cases i <;> norm_num [est₀, w₀, abs_le]

/-- Boundary: a negative critical value gives the empty band on a nonempty grid. -/
example (f : Fin 2 → ℝ) : f ∉ simultaneousBand est₀ w₀ (-1) 4 := fun h => by
  have h0 := h 0
  rw [sqrt_four] at h0
  norm_num [w₀] at h0
  linarith [abs_nonneg (est₀ 0 - f 0)]

/-- The weighted sup statistic computed from the definition: `max(|3| / 1, |-4| / 2) = 3`. -/
example : weightedSup ![1, 2] ![3, -4] = 3 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    fin_cases i <;> norm_num
  · have h := norm_le_pi_norm (fun i => (![3, -4] : Fin 2 → ℝ) i / (![1, 2] : Fin 2 → ℝ) i) 0
    norm_num at h
    exact h

/-- Consistency of `mem_simultaneousBand_iff` with the direct computation: the scaled weighted
sup statistic at `(1.25, 2.4)` is `max(2 · 0.25, 2 · 0.4) = 0.8 ≤ 1`. -/
example : weightedSup w₀ (√((4 : ℕ) : ℝ) • (est₀ - ![1.25, 2.4])) ≤ 1 :=
  (mem_simultaneousBand_iff (fun i => by fin_cases i <;> norm_num [w₀]) (by norm_num)).1
    (by intro i; rw [sqrt_four]; fin_cases i <;> norm_num [est₀, w₀, abs_le])

/-- On a one-point grid the band is the pointwise interval. -/
example (est w : Unit → ℝ) (c : ℝ) (n : ℕ) :
    simultaneousBand est w c n = (fun f : Unit → ℝ => f ()) ⁻¹' pointwiseInterval est w c n () :=
  simultaneousBand_eq_of_subsingleton est w c n ()

/-! ### Strict inequality between simultaneous and pointwise limit coverage

The limit `Z` takes the values `(1, 0)` and `(0, 1)` with probability `1/2` each; with unit
weights and `c = 1/2`, pointwise limit coverage is `1/2` at each grid point while simultaneous
limit coverage is `0`. Both values are computed from the definitions. -/

/-- The two-point law. -/
noncomputable def P₀ : Measure (Fin 2) :=
  (1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac 1

/-- The limit vector: `Z 0 = (1, 0)`, `Z 1 = (0, 1)`. -/
noncomputable def Z₀ : Fin 2 → Fin 2 → ℝ := fun ω i => if ω = i then 1 else 0

private theorem weightedSup_Z₀ (ω : Fin 2) : weightedSup (fun _ => 1) (Z₀ ω) = 1 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    simp only [Z₀, div_one, Real.norm_eq_abs]
    split_ifs <;> norm_num
  · have h := norm_le_pi_norm (fun i => Z₀ ω i / (fun _ : Fin 2 => (1 : ℝ)) i) ω
    simpa [weightedSup, Z₀] using h

example : P₀ {ω | weightedSup (fun _ => 1) (Z₀ ω) ≤ 1 / 2} = 0 := by
  have : {ω : Fin 2 | weightedSup (fun _ => 1) (Z₀ ω) ≤ 1 / 2} = ∅ := by
    ext ω
    simp only [weightedSup_Z₀, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    norm_num
  rw [this, measure_empty]

example : P₀ {ω | |Z₀ ω 0 / (fun _ : Fin 2 => (1 : ℝ)) 0| ≤ 1 / 2} = 1 / 2 := by
  have : {ω : Fin 2 | |Z₀ ω 0 / (fun _ : Fin 2 => (1 : ℝ)) 0| ≤ 1 / 2} = {1} := by
    ext ω
    fin_cases ω <;> norm_num [Z₀]
  rw [this]
  simp [P₀]

/-! ### Equality case: a perfectly correlated limit -/

example (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (ξ : Ω' → ℝ) (c : ℝ) :
    P' {ω | weightedSup ![1, 2] (ξ ω • ![1, 2]) ≤ c} =
      P' {ω | |(ξ ω • (![1, 2] : Fin 2 → ℝ)) 1 / (![1, 2] : Fin 2 → ℝ) 1| ≤ c} :=
  measure_weightedSup_le_eq_of_proportional (fun i => by fin_cases i <;> norm_num)
    (fun _ => rfl) c 1

/-! ### Critical values -/

/-- Boundary, from the definition: outside `α ∈ (0, 1)` the critical value is `0`. -/
example (μ : Measure ℝ) : criticalValue μ 1 = 0 := by
  simp [criticalValue, cdfQuantile]

/-- Non-vacuity: the standard Gaussian is atomless, so its `0.95` critical value has cdf
exactly `0.95`. -/
example : cdf (gaussianReal 0 1) (criticalValue (gaussianReal 0 1) 0.05) = 1 - 0.05 :=
  cdf_criticalValue _ ⟨by norm_num, by norm_num⟩ fun _ =>
    gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton

/-! ### The Hall–Wellner transformation -/

/-- From the definition: `K(0) = 0` (boundary) and `K(1) = 1/2`. -/
example : hallWellnerTime 0 = 0 ∧ hallWellnerTime 1 = 1 / 2 := by
  norm_num [hallWellnerTime]

example : hallWellnerTime 3 < 1 := hallWellnerTime_lt_one (by norm_num)

/-- The one-point-grid process `Z ω () = ω`. -/
def Zg : ℝ → Unit → ℝ := fun ω _ => ω

/-- Non-vacuity on a one-point grid with `Z = ξ` standard Gaussian, so `σ² = 1`: the theorem gives
`Var(ξ / 2) = K(1) (1 - K(1)) = 1/4`, matching the direct computation below. -/
example : cov[fun ω => Zg ω () / (1 + 1), fun ω => Zg ω () / (1 + 1); gaussianReal 0 1] =
    1 / 4 := by
  have hcov : ∀ i j : Unit, cov[fun ω => Zg ω i, fun ω => Zg ω j; gaussianReal 0 1] =
      (fun _ : Unit => (1 : ℝ)) (min i j) := fun _ _ => by
    change cov[id, id; gaussianReal 0 1] = 1
    rw [covariance_self aemeasurable_id]
    exact_mod_cast variance_id_gaussianReal
  rw [covariance_div_hallWellner_nelsonAalen (σ2 := fun _ : Unit => (1 : ℝ))
    (fun _ => zero_le_one) hcov le_rfl]
  norm_num [hallWellnerTime]

/-- The same variance computed directly, without the theorem. -/
example : cov[fun ω : ℝ => ω / (1 + 1), fun ω : ℝ => ω / (1 + 1); gaussianReal 0 1] = 1 / 4 := by
  simp only [div_eq_mul_inv]
  rw [covariance_mul_const_left, covariance_mul_const_right, covariance_self aemeasurable_id']
  rw [show (fun ω : ℝ => ω) = id from rfl, variance_id_gaussianReal]
  norm_num

/-- **Law level, non-vacuity.** On a one-point grid with `Z = ξ` standard Gaussian and `σ² = 1`,
the Hall–Wellner weighted limit `ξ / 2` has law `multivariateGaussian 0 (hallWellnerCov 1)`, and
that matrix is the `1 × 1` matrix `K(1) (1 - K(1)) = 1/4`. -/
example : (gaussianReal 0 1).map (fun ω => WithLp.toLp 2 (fun i => Zg ω i / (1 + 1))) =
      multivariateGaussian 0 (hallWellnerCov (fun _ : Unit => (1 : ℝ))) ∧
    hallWellnerCov (fun _ : Unit => (1 : ℝ)) () () = 1 / 4 := by
  refine ⟨?_, by norm_num [hallWellnerCov, hallWellnerTime]⟩
  have hZ : HasGaussianLaw Zg (gaussianReal 0 1) :=
    IsGaussian.hasGaussianLaw_id.map_fun
      (ContinuousLinearMap.pi fun _ : Unit => ContinuousLinearMap.id ℝ ℝ)
  have hcov : ∀ i j : Unit, cov[fun ω => Zg ω i, fun ω => Zg ω j; gaussianReal 0 1] =
      (fun _ : Unit => (1 : ℝ)) (min i j) := fun _ _ => by
    change cov[id, id; gaussianReal 0 1] = 1
    rw [covariance_self aemeasurable_id]
    exact_mod_cast variance_id_gaussianReal
  exact map_div_hallWellner_eq_multivariateGaussian (σ2 := fun _ : Unit => (1 : ℝ))
    (fun _ => zero_le_one) hZ (fun _ => integral_id_gaussianReal) hcov

/-! ### A concrete atomless limit -/

/-- The limit `Z = ξ • 1` on the two-point grid with `ξ ~ N(0, 1)`. -/
def Zc : ℝ → Fin 2 → ℝ := fun ω _ => ω

private theorem weightedSup_Zc (ω : ℝ) : weightedSup w₀ (Zc ω) = |ω| := by
  have : (fun i => Zc ω i / w₀ i) = fun _ => ω := funext fun i => by
    fin_cases i <;> simp [Zc, w₀]
  rw [weightedSup, this, pi_norm_const, Real.norm_eq_abs]

/-- **`hatom` holds on a concrete limit**: for `Z = ξ • 1`, the weighted sup is `|ξ|`, and
`P(|ξ| = c) = 0` because the Gaussian law has no atoms. -/
theorem hatom_Zc (c : ℝ) : gaussianReal 0 1 {ω | weightedSup w₀ (Zc ω) = c} = 0 := by
  let _ := nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)
  refine measure_mono_null (t := {c, -c}) (fun ω hω => ?_)
    (((Set.countable_singleton (-c)).insert c).measure_zero _)
  simp only [mem_ofPred_eq, weightedSup_Zc] at hω
  rcases abs_eq_abs.1 (hω.trans (abs_of_nonneg (hω ▸ abs_nonneg ω)).symm) with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa using h)

/-! ### Asymptotic theorems: hypotheses are dischargeable -/

/-- The known-weight band theorem applies to any grid limit; here instantiated on the two-point
grid with unit weights. -/
example (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] (est : ℕ → Ω → Fin 2 → ℝ) (θ : Fin 2 → ℝ)
    (Z : Ω' → Fin 2 → ℝ)
    (hZ : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (est n ω - θ)) atTop Z
      (fun _ => P) P')
    (hatom : P' {ω | weightedSup w₀ (Z ω) = 1} = 0) :
    Tendsto (fun n => P {ω | θ ∈ simultaneousBand (est n ω) w₀ 1 n}) atTop
      (𝓝 (P' {ω | weightedSup w₀ (Z ω) ≤ 1})) :=
  tendsto_coverage_simultaneousBand_const hZ (fun i => by fin_cases i <;> norm_num [w₀]) hatom

/-- The known-weight theorem with the atomless hypothesis discharged on the concrete limit
`Z = ξ • 1`, `ξ ~ N(0, 1)`: only the grid limit itself remains a hypothesis. -/
example (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (est : ℕ → Ω → Fin 2 → ℝ) (θ : Fin 2 → ℝ) (c : ℝ)
    (hZ : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (est n ω - θ)) atTop Zc
      (fun _ => P) (gaussianReal 0 1)) :
    Tendsto (fun n => P {ω | θ ∈ simultaneousBand (est n ω) w₀ c n}) atTop
      (𝓝 (gaussianReal 0 1 {ω | |ω| ≤ c})) := by
  have h := tendsto_coverage_simultaneousBand_const hZ
    (fun i => by fin_cases i <;> norm_num [w₀]) (hatom_Zc c)
  simpa only [weightedSup_Zc] using h

open MathlibExt.Probability.Statistics.AalenJohansenCLT MathlibExt.Probability.Statistics.Censoring
  MathlibExt.Probability.Statistics.SurvivalConsistency in
/-- The Kaplan–Meier band theorem applied with known unit weights and a fixed critical value
(constant sequences converge in probability), on the grid `{j ≤ m}`. -/
example {k r : ℕ} (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → (Fin k × Fin r) × Fin k) (pTJ : PMF (Fin k × Fin r)) (pC : PMF (Fin k))
    (hind : iIndepFun W P) (hlaw : ∀ i, HasLaw (W i) (indepCauseLaw pTJ pC) P) (m : Fin k)
    (hm : causeAtRiskMass (indepCauseLaw pTJ pC) m ≠ 0) (c : ℝ) :
    ∃ Y : EuclideanSpace ℝ (Cell k r) → {j : Fin k // j ≤ m} → ℝ,
      stdGaussian (EuclideanSpace ℝ (Cell k r)) {z | weightedSup (fun _ => 1) (Y z) = c} = 0 →
      Tendsto (fun n => P {ω | (fun j => target pTJ m (none, j)) ∈
          simultaneousBand (fun j => estimator m (empiricalCauseData W n ω) (none, j))
            (fun _ => 1) c n})
        atTop (𝓝 (stdGaussian (EuclideanSpace ℝ (Cell k r))
          {z | weightedSup (fun _ => 1) (Y z) ≤ c})) := by
  obtain ⟨Y, -, -, h⟩ := tendsto_coverage_kaplanMeierBand_indepCauseLaw pTJ pC hind hlaw m hm
  exact ⟨Y, fun hatom => h (ŵ := fun _ _ _ => 1) (ĉ := fun _ _ => c) (fun _ => one_pos)
    (tendstoInMeasure_const_self _) (fun _ => aemeasurable_const) (tendstoInMeasure_const_self c)
    (fun _ => aemeasurable_const) hatom⟩

open MathlibExt.Probability.Statistics.AalenJohansenCLT MathlibExt.Probability.Statistics.Censoring
  MathlibExt.Probability.Statistics.SurvivalConsistency in
/-- The Kaplan–Meier grid limit of the band theorem is centered: from its linear-combination laws,
every coordinate `Y j` has mean `0`. -/
example {k r : ℕ} (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → (Fin k × Fin r) × Fin k) (pTJ : PMF (Fin k × Fin r)) (pC : PMF (Fin k))
    (hind : iIndepFun W P) (hlaw : ∀ i, HasLaw (W i) (indepCauseLaw pTJ pC) P) (m : Fin k)
    (hm : causeAtRiskMass (indepCauseLaw pTJ pC) m ≠ 0) :
    ∃ Y : EuclideanSpace ℝ (Cell k r) → {j : Fin k // j ≤ m} → ℝ,
      ∀ j, ∫ z, Y z j ∂stdGaussian (EuclideanSpace ℝ (Cell k r)) = 0 := by
  classical
  obtain ⟨Y, -, hlin, -⟩ := tendsto_coverage_kaplanMeierBand_indepCauseLaw pTJ pC hind hlaw m hm
  refine ⟨Y, fun j => ?_⟩
  have h := hlin (Pi.single j 1)
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h
  rw [h.integral_eq, integral_id_gaussianReal]

end MathlibExtTest.Probability.Statistics.SimultaneousBands
