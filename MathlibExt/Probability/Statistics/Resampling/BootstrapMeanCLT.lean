/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LindebergFeller
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Uniform
public import MathlibExt.Probability.FiniteProbability

/-!
# Bootstrap mean CLT for a deterministic sequence

Let `x : ℕ → ℝ` have Cesàro means `x̄ₙ → m` and Cesàro second moments
`n⁻¹ ∑_{i<n} x i ^ 2 → s ^ 2 + m ^ 2` with `s > 0`. If `Y₁, …, Yₙ` are i.i.d. from the empirical
law `νₙ = n⁻¹ ∑_{i<n} δ_{x i}`, then `√n (Ȳ - x̄ₙ)` converges weakly to `N(0, s ^ 2)`.

The row law `νₙ` changes with `n`, so the fixed-law i.i.d. CLT does not apply. The proof builds
the triangular array `(Yₙₖ - x̄ₙ) / √n` on one product space (`bootstrapMeasure`), checks the
hypotheses of `ProbabilityTheory.lindeberg_feller_clt_triangular`, and applies it.

## Main statements

* `ProbabilityTheory.empiricalLaw` (Mathlib's `Measure.uniformOfFinset` pushed forward by `x`),
  `ProbabilityTheory.empiricalMean` (`FiniteProbability.sampleMean` of the first `n` terms),
  `ProbabilityTheory.bootstrapMeasure`, `ProbabilityTheory.bootstrapRow`.
* `ProbabilityTheory.lindebergConditionTriangular_bootstrapRow`: the Lindeberg condition, from
  Cesàro convergence of `x i ^ 2` alone.
* `ProbabilityTheory.tendsto_integral_map_sum_bootstrapRow`: the CLT on the coupling space.
* `ProbabilityTheory.tendsto_integral_bootstrapMean_law`: the CLT for the bootstrap law
  `νₙ^{⊗n}` mapped by `y ↦ √n (n⁻¹ ∑ y i - x̄ₙ)`.

Random original data (bootstrap consistency in probability or almost surely, quantiles, coverage)
is not covered here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex Finset
open scoped Topology BoundedContinuousFunction NNReal ENNReal

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction NNReal ENNReal

/-- The empirical law of the first `n` terms of a real sequence `x`: the uniform law on
`{0, …, n - 1}` pushed forward by `x`, i.e. `(1 / n) ∑_{i < n} δ_{x i}` (`empiricalLaw_eq`).
For `n = 0` it is the zero measure. -/
noncomputable def empiricalLaw (x : ℕ → ℝ) (n : ℕ) : Measure ℝ :=
  (Measure.uniformOfFinset (Finset.range n)).map x

/-- `empiricalLaw x n = (1 / n) ∑_{i < n} δ_{x i}`. -/
theorem empiricalLaw_eq (x : ℕ → ℝ) (n : ℕ) :
    empiricalLaw x n = (n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (x i) := by
  ext s hs
  rw [empiricalLaw, Measure.map_apply measurable_from_nat hs, Measure.uniformOfFinset,
    Measure.smul_apply, Measure.finsetSum_apply, Measure.finsetSum_apply, Finset.card_range,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurable_from_nat hs),
    Measure.dirac_apply' _ hs]
  rfl

/-- The empirical mean of the first `n` terms of `x`: the finite sample mean of
`x 0, …, x (n - 1)` (zero for `n = 0`). -/
noncomputable def empiricalMean (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  MathlibExt.Probability.FiniteProbability.sampleMean (fun i : Fin n => x i)

/-- `empiricalMean x n = (1 / n) ∑_{i < n} x i`. -/
theorem empiricalMean_eq (x : ℕ → ℝ) (n : ℕ) :
    empiricalMean x n = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i := by
  rw [empiricalMean, MathlibExt.Probability.FiniteProbability.sampleMean_eq_sum_div,
    Fintype.card_fin, Fin.sum_univ_eq_sum_range (fun i => x i) n, div_eq_inv_mul]

/-- For `n ≥ 1` the empirical law is a probability measure. -/
theorem isProbabilityMeasure_empiricalLaw (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (empiricalLaw x n) := by
  constructor
  rw [empiricalLaw_eq, Measure.smul_apply, Measure.finsetSum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

/-- The row laws of the bootstrap space: row `n` resamples from the empirical law of
`x 0, …, x (n - 1)`; the empty row `n = 0` uses the law of `x 0` so that every factor is a
probability measure. -/
instance isProbabilityMeasure_empiricalLaw_max_one (x : ℕ → ℝ) (n : ℕ) :
    IsProbabilityMeasure (empiricalLaw x (max n 1)) := by
  exact isProbabilityMeasure_empiricalLaw x (lt_of_lt_of_le Nat.one_pos (le_max_right n 1))

/-- The bootstrap coupling space: coordinate `ω n k` is the `k`-th resampled value in row `n`;
all coordinates are independent, and every coordinate in row `n` has law
`empiricalLaw x (max n 1)`. -/
noncomputable def bootstrapMeasure (x : ℕ → ℝ) : Measure (ℕ → ℕ → ℝ) :=
  Measure.infinitePi fun n : ℕ => Measure.infinitePi fun _ : ℕ => empiricalLaw x (max n 1)

/-- The triangular-array entry `(Y_{n k} - x̄_n) / √n` of the bootstrap mean. -/
noncomputable def bootstrapRow (x : ℕ → ℝ) (n k : ℕ) (ω : ℕ → ℕ → ℝ) : ℝ :=
  (ω n k - empiricalMean x n) / Real.sqrt n

private instance isProbabilityMeasure_bootstrapMeasure (x : ℕ → ℝ) :
    IsProbabilityMeasure (bootstrapMeasure x) := by
  unfold bootstrapMeasure
  infer_instance

private lemma measurable_coord (n k : ℕ) : Measurable (fun ω : ℕ → ℕ → ℝ => ω n k) :=
  (measurable_pi_apply k).comp (measurable_pi_apply n)

private lemma measurePreserving_coord (x : ℕ → ℝ) (n k : ℕ) :
    MeasurePreserving (fun ω : ℕ → ℕ → ℝ => ω n k) (bootstrapMeasure x)
      (empiricalLaw x (max n 1)) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => empiricalLaw x (max n 1)) k).comp
    (measurePreserving_eval_infinitePi
      (fun n : ℕ => Measure.infinitePi fun _ : ℕ => empiricalLaw x (max n 1)) n)

private lemma integral_empiricalLaw (x : ℕ → ℝ) (n : ℕ) (g : ℝ → ℝ) :
    ∫ y, g y ∂(empiricalLaw x n) = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, g (x i) := by
  rw [empiricalLaw_eq, integral_smul_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac enorm_lt_top)]
  simp [integral_dirac, ENNReal.toReal_inv]

private lemma integrable_empiricalLaw (x : ℕ → ℝ) (n : ℕ) (g : ℝ → ℝ) :
    Integrable g (empiricalLaw x n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [empiricalLaw_eq]
  · rw [empiricalLaw_eq]
    exact (integrable_finsetSum_measure.2 fun i _ => integrable_dirac enorm_lt_top).smul_measure
      (ENNReal.inv_ne_top.2 (by exact_mod_cast hn.ne'))

private lemma integral_bootstrapRow_comp (x : ℕ → ℝ) (n k : ℕ) {g : ℝ → ℝ}
    (hg : Measurable g) :
    ∫ ω, g (bootstrapRow x n k ω) ∂(bootstrapMeasure x) =
      ∫ y, g ((y - empiricalMean x n) / Real.sqrt n) ∂(empiricalLaw x (max n 1)) := by
  rw [← (measurePreserving_coord x n k).map_eq,
    integral_map (f := fun y => g ((y - empiricalMean x n) / Real.sqrt n))
      (measurable_coord n k).aemeasurable
      (hg.comp ((measurable_id.sub_const _).div_const _)).aestronglyMeasurable]
  rfl

private lemma integrable_bootstrapRow_comp (x : ℕ → ℝ) (n k : ℕ) {g : ℝ → ℝ}
    (hg : Measurable g) :
    Integrable (fun ω => g (bootstrapRow x n k ω)) (bootstrapMeasure x) :=
  ((measurePreserving_coord x n k).integrable_comp
    (g := fun y => g ((y - empiricalMean x n) / Real.sqrt n))
    (hg.comp ((measurable_id.sub_const _).div_const _)).aestronglyMeasurable).2
    (integrable_empiricalLaw x _ _)

private lemma map_restrict_row (x : ℕ → ℝ) (n : ℕ) :
    Measure.map (fun ω : ℕ → ℕ → ℝ => (Finset.range n).restrict (ω n)) (bootstrapMeasure x) =
      Measure.pi fun _ : Finset.range n => empiricalLaw x (max n 1) := by
  have h1 : Measure.map (fun ω : ℕ → ℕ → ℝ => ω n) (bootstrapMeasure x) =
      Measure.infinitePi fun _ : ℕ => empiricalLaw x (max n 1) :=
    (measurePreserving_eval_infinitePi
      (fun n : ℕ => Measure.infinitePi fun _ : ℕ => empiricalLaw x (max n 1)) n).map_eq
  calc Measure.map (fun ω : ℕ → ℕ → ℝ => (Finset.range n).restrict (ω n)) (bootstrapMeasure x)
      = Measure.map (Finset.range n).restrict
          (Measure.map (fun ω : ℕ → ℕ → ℝ => ω n) (bootstrapMeasure x)) := by
        rw [Measure.map_map (Finset.measurable_restrict (X := fun _ : ℕ => ℝ) _)
          (measurable_pi_apply n)]
        rfl
    _ = Measure.pi fun _ : Finset.range n => empiricalLaw x (max n 1) := by
        rw [h1, Measure.infinitePi_map_restrict]

private lemma iIndepFun_coord_row (x : ℕ → ℝ) (n : ℕ) :
    iIndepFun (fun (k : Finset.range n) (ω : ℕ → ℕ → ℝ) => ω n k) (bootstrapMeasure x) := by
  refine (iIndepFun_iff_map_fun_eq_pi_map
    (fun k : Finset.range n => (measurable_coord n k).aemeasurable)).2 ?_
  refine (map_restrict_row x n).trans ?_
  congr 1
  funext k
  exact ((measurePreserving_coord x n k).map_eq).symm

theorem iIndepFun_bootstrapRow (x : ℕ → ℝ) (n : ℕ) :
    iIndepFun (m := fun _ => inferInstance) ((Finset.range n).restrict (bootstrapRow x n))
      (bootstrapMeasure x) := by
  exact (iIndepFun_coord_row x n).comp (fun _ y => (y - empiricalMean x n) / Real.sqrt n)
    (fun _ => (measurable_id.sub_const _).div_const _)

theorem measurable_bootstrapRow (x : ℕ → ℝ) (n k : ℕ) : Measurable (bootstrapRow x n k) := by
  exact ((measurable_coord n k).sub_const _).div_const _

theorem integral_bootstrapRow (x : ℕ → ℝ) {n k : ℕ} (hk : k ∈ Finset.range n) :
    ∫ ω, bootstrapRow x n k ω ∂(bootstrapMeasure x) = 0 := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) (Finset.mem_range.1 hk)
  rw [integral_bootstrapRow_comp x n k (g := fun t => t) measurable_id, max_eq_left hn,
    integral_empiricalLaw, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, empiricalMean_eq]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

theorem integrable_bootstrapRow_sq (x : ℕ → ℝ) (n k : ℕ) :
    Integrable (fun ω => (bootstrapRow x n k ω) ^ 2) (bootstrapMeasure x) := by
  exact integrable_bootstrapRow_comp x n k (g := fun t => t ^ 2) (measurable_id.pow_const 2)

private lemma sum_sq_sub_empiricalMean (x : ℕ → ℝ) (n : ℕ) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (x i - empiricalMean x n) ^ 2 =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i ^ 2 - empiricalMean x n ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [empiricalMean_eq]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, empiricalMean_eq]
    field_simp
    ring

private lemma sum_integral_bootstrapRow_sq_eq (x : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, ∫ ω, (bootstrapRow x n k ω) ^ 2 ∂(bootstrapMeasure x) =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i ^ 2 - empiricalMean x n ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [empiricalMean_eq]
  · have hterm : ∀ k, ∫ ω, (bootstrapRow x n k ω) ^ 2 ∂(bootstrapMeasure x) =
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((x i - empiricalMean x n) / Real.sqrt n) ^ 2 := by
      intro k
      rw [integral_bootstrapRow_comp x n k (g := fun t => t ^ 2) (measurable_id.pow_const 2),
        max_eq_left hn, integral_empiricalLaw]
    have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [← sum_sq_sub_empiricalMean, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    simp only [div_pow, hs, ← Finset.sum_div]
    field_simp

theorem tendsto_sum_integral_bootstrapRow_sq (x : ℕ → ℝ) {m s : ℝ}
    (hmean : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i) atTop (𝓝 m))
    (hsq : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i ^ 2) atTop
      (𝓝 (s ^ 2 + m ^ 2))) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, ∫ ω, (bootstrapRow x n k ω) ^ 2 ∂(bootstrapMeasure x))
      atTop (𝓝 (s ^ 2)) := by
  have h := hsq.sub (hmean.pow 2)
  rw [add_sub_cancel_right] at h
  refine h.congr fun n => ?_
  rw [sum_integral_bootstrapRow_sq_eq, empiricalMean_eq]

private lemma eventually_sq_le_mul (x : ℕ → ℝ) {c : ℝ}
    (hsq : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i ^ 2) atTop (𝓝 c))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.range n, x i ^ 2 ≤ δ * n := by
  set a : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i ^ 2 with ha
  have hS : ∀ n : ℕ, ∑ i ∈ Finset.range n, x i ^ 2 = n * a n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp only [ha]
      field_simp
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hsq (δ / 4) (by positivity)
  set M := ∑ j ∈ Finset.range N, x j ^ 2
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => sq_nonneg (x j)
  have hbound : ∀ i : ℕ, x i ^ 2 ≤ M + |c| + (2 * i + 1) * (δ / 4) := by
    intro i
    by_cases hi : i < N
    · have h1 : x i ^ 2 ≤ M :=
        Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j))
          (Finset.mem_range.2 hi)
      have h2 : 0 ≤ (2 * (i : ℝ) + 1) * (δ / 4) := by positivity
      linarith [abs_nonneg c]
    · replace hi : N ≤ i := not_lt.1 hi
      have h1 := hN i hi
      have h2 := hN (i + 1) (by omega)
      rw [Real.dist_eq, abs_lt] at h1 h2
      have hx : x i ^ 2 = ((i : ℝ) + 1) * a (i + 1) - (i : ℝ) * a i := by
        have e1 := hS (i + 1)
        have e2 := hS i
        rw [Finset.sum_range_succ] at e1
        push_cast at e1
        linarith
      have h3 : 0 ≤ ((i : ℝ) + 1) * (δ / 4 - (a (i + 1) - c)) :=
        mul_nonneg (by positivity) (by linarith)
      have h4 : 0 ≤ (i : ℝ) * (δ / 4 + (a i - c)) := mul_nonneg (by positivity) (by linarith)
      nlinarith [le_abs_self c]
  have hev : ∀ᶠ n : ℕ in atTop, M + |c| ≤ δ / 2 * n :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop
      (by positivity : (0 : ℝ) < δ / 2)).eventually_ge_atTop (M + |c|)
  filter_upwards [hev] with n hn i hi
  have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hi
  have h5 : (2 * (i : ℝ) + 1) * (δ / 4) ≤ (2 * n) * (δ / 4) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith [hbound i]

private lemma abs_bootstrapRow_point_le (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ i ∈ Finset.range n, x i ^ 2 ≤ ε ^ 2 / 4 * n) {i : ℕ} (hi : i ∈ Finset.range n) :
    |(x i - empiricalMean x n) / Real.sqrt n| ≤ ε := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ j ∈ Finset.range n, x j ^ 2 ≤ n * (ε ^ 2 / 4 * n) := by
    have := Finset.sum_le_sum h
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hmean2 : empiricalMean x n ^ 2 ≤ ε ^ 2 / 4 * n := by
    have h1 := sum_sq_sub_empiricalMean x n
    have h2 : 0 ≤ (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, (x j - empiricalMean x n) ^ 2 :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => sq_nonneg _)
    have h3 : (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, x j ^ 2 ≤ ε ^ 2 / 4 * n := by
      rw [inv_mul_le_iff₀ hn']
      exact hsum
    linarith
  have hdiff : (x i - empiricalMean x n) ^ 2 ≤ ε ^ 2 * n := by
    nlinarith [h i hi, sq_nonneg (x i + empiricalMean x n)]
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hsq : ((x i - empiricalMean x n) / Real.sqrt n) ^ 2 ≤ ε ^ 2 := by
    rw [div_pow, hs, div_le_iff₀ hn']
    exact hdiff
  have habs := sq_le_sq.1 hsq
  rwa [abs_of_pos hε] at habs

theorem lindebergConditionTriangular_bootstrapRow (x : ℕ → ℝ) {c : ℝ}
    (hsq : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i ^ 2) atTop (𝓝 c)) :
    LindebergConditionTriangular (bootstrapRow x) (bootstrapMeasure x) := by
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_sq_le_mul x hsq (δ := ε ^ 2 / 4) (by positivity),
    eventually_gt_atTop 0] with n hn hn0
  refine (Finset.sum_eq_zero fun k _ => ?_).symm
  have hind : ∀ ω, Set.indicator {ω' | ε < |bootstrapRow x n k ω'|}
      (1 : (ℕ → ℕ → ℝ) → ℝ) ω = Set.indicator {t : ℝ | ε < |t|} 1 (bootstrapRow x n k ω) := by
    intro ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  simp_rw [hind]
  have hmeas : Measurable (fun t : ℝ => t ^ 2 * Set.indicator {t : ℝ | ε < |t|} 1 t) :=
    (measurable_id.pow_const 2).mul
      (measurable_const.indicator (measurableSet_lt measurable_const continuous_abs.measurable))
  rw [integral_bootstrapRow_comp x n k hmeas, max_eq_left hn0, integral_empiricalLaw]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i hi => ?_)
  have hle := abs_bootstrapRow_point_le x hn0 hε hn hi
  simp [not_lt.2 hle]

theorem tendsto_integral_map_sum_bootstrapRow (x : ℕ → ℝ) {m s : ℝ} (hs : 0 < s)
    (hmean : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i) atTop (𝓝 m))
    (hsq : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i ^ 2) atTop
      (𝓝 (s ^ 2 + m ^ 2))) :
    ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ y, f y ∂(Measure.map
          (fun ω => ∑ k ∈ Finset.range n, bootstrapRow x n k ω) (bootstrapMeasure x)))
        atTop (𝓝 (∫ y, f y ∂(gaussianReal 0 ⟨s ^ 2, sq_nonneg s⟩))) := by
  exact lindeberg_feller_clt_triangular (bootstrapRow x) (fun n => iIndepFun_bootstrapRow x n)
    (fun n k _ => measurable_bootstrapRow x n k) (fun n k hk => integral_bootstrapRow x hk)
    (fun n k _ => integrable_bootstrapRow_sq x n k) s hs
    (tendsto_sum_integral_bootstrapRow_sq x hmean hsq)
    (lindebergConditionTriangular_bootstrapRow x hsq)

private lemma map_fin_row (x : ℕ → ℝ) (n : ℕ) :
    Measure.map (fun (ω : ℕ → ℕ → ℝ) (i : Fin n) => ω n i) (bootstrapMeasure x) =
      Measure.pi fun _ : Fin n => empiricalLaw x (max n 1) := by
  have hind : iIndepFun (fun (i : Fin n) (ω : ℕ → ℕ → ℝ) => ω n i) (bootstrapMeasure x) :=
    (iIndepFun_coord_row x n).precomp
      (g := fun i : Fin n => (⟨i, Finset.mem_range.2 i.isLt⟩ : Finset.range n))
      (fun i j h => Fin.ext (congrArg Subtype.val h))
  rw [hind.map_fun_eq_pi_map (fun i : Fin n => (measurable_coord n i).aemeasurable)]
  congr 1
  funext i
  exact (measurePreserving_coord x n i).map_eq

theorem map_sum_bootstrapRow_eq (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    Measure.map (fun ω => ∑ k ∈ Finset.range n, bootstrapRow x n k ω) (bootstrapMeasure x) =
      Measure.map
        (fun y : Fin n → ℝ => Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i, y i - empiricalMean x n))
        (Measure.pi fun _ : Fin n => empiricalLaw x n) := by
  have h := map_fin_row x n
  rw [max_eq_left hn] at h
  have hF : Measurable
      (fun y : Fin n → ℝ => Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i, y i - empiricalMean x n)) := by
    fun_prop
  have hP : Measurable (fun (ω : ℕ → ℕ → ℝ) (i : Fin n) => ω n i) :=
    Measurable.of_eval fun i => measurable_coord n i
  rw [← h, Measure.map_map hF hP]
  congr 1
  funext ω
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hpos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  simp only [Function.comp_apply, bootstrapRow, Fin.sum_univ_eq_sum_range (fun k => ω n k) n,
    ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  generalize Real.sqrt n = t at hs hpos ⊢
  rw [← hs]
  have ht : t ≠ 0 := hpos.ne'
  field_simp

theorem tendsto_integral_bootstrapMean_law (x : ℕ → ℝ) {m s : ℝ} (hs : 0 < s)
    (hmean : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i) atTop (𝓝 m))
    (hsq : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i ^ 2) atTop
      (𝓝 (s ^ 2 + m ^ 2))) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ y, f y ∂(Measure.map
        (fun y : Fin n → ℝ => Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i, y i - empiricalMean x n))
        (Measure.pi fun _ : Fin n => empiricalLaw x n)))
      atTop (𝓝 (∫ y, f y ∂(gaussianReal 0 ⟨s ^ 2, sq_nonneg s⟩))) := by
  refine (tendsto_integral_map_sum_bootstrapRow x hs hmean hsq f).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [map_sum_bootstrapRow_eq x hn]

end ProbabilityTheory
