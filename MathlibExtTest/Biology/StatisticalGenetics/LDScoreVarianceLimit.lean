/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreVarianceLimit
public import MathlibExt.Biology.StatisticalGenetics.LDScoreDesignSequence

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open MathlibExt.Probability.FiniteProbability
  MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
  MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
  MathlibExt.Biology.StatisticalGenetics.LDScoreVariance
  MathlibExt.Biology.StatisticalGenetics.LDScoreDesignSequence
  MathlibExt.Biology.StatisticalGenetics.LDScoreVarianceLimit
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.LDScoreVarianceLimit

/-! ### The score law `½ (δ₀ + δ₂)`

Scores are the coordinates of `ℕ → ℝ` under the i.i.d. product of `ν2 = ½ (δ₀ + δ₂)`, so
`z ∈ {0, 2}`, `𝔼 z² = 2`, `𝔼 z⁴ = 8` and `Var(z²) = 4`, all computed from the definitions. -/

/-- The law `½ (δ₀ + δ₂)`. -/
noncomputable def ν2 : Measure ℝ := (2⁻¹ : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac 2)

instance : IsProbabilityMeasure ν2 :=
  ⟨by
    rw [ν2, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ,
      one_add_one_eq_two, smul_eq_mul]
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top⟩

theorem integral_ν2 (f : ℝ → ℝ) : ∫ x, f x ∂ν2 = (f 0 + f 2) / 2 := by
  rw [ν2, integral_smul_measure,
    integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac]
  simp [ENNReal.toReal_inv]
  ring

theorem ae_abs_le_ν2 : ∀ᵐ x ∂ν2, |x| ≤ 2 := by
  rw [ν2]
  refine Measure.ae_smul_measure (ae_add_measure_iff.2 ⟨?_, ?_⟩) _
  · rw [ae_dirac_eq]
    simp
  · rw [ae_dirac_eq]
    norm_num

theorem memLp_coord_four (s : ℕ) : MemLp (fun ω : ℕ → ℝ => ω s) 4 (coordMeasure ν2) := by
  refine MemLp.of_bound (measurable_pi_apply s).aestronglyMeasurable 2 ?_
  have h : ∀ᵐ x ∂(coordMeasure ν2).map (fun ω => ω s), |x| ≤ 2 := by
    rw [map_coord]
    exact ae_abs_le_ν2
  exact (ae_of_ae_map (measurable_pi_apply s).aemeasurable h).mono fun ω hω => by
    simpa [Real.norm_eq_abs] using hω

theorem integral_coord_pow (s p : ℕ) :
    ∫ ω, ω s ^ p ∂coordMeasure ν2 = ((0 : ℝ) ^ p + 2 ^ p) / 2 := by
  have h := integral_map (μ := coordMeasure ν2) (measurable_pi_apply s).aemeasurable
    (f := fun x : ℝ => x ^ p) (by fun_prop)
  rw [map_coord] at h
  rw [← h, integral_ν2]

/-- `𝔼 z⁴ = 8`. -/
theorem integral_coord_sq_sq (s : ℕ) : ∫ ω, (ω s ^ 2) ^ 2 ∂coordMeasure ν2 = 8 := by
  simp only [← pow_mul]
  rw [integral_coord_pow]
  norm_num

/-- `Var(z²) = 𝔼 z⁴ - (𝔼 z²)² = 8 - 4 = 4`. -/
theorem variance_coord_sq (s : ℕ) :
    Var[fun ω : ℕ → ℝ => ω s ^ 2; coordMeasure ν2] = 4 := by
  rw [variance_eq_sub (memLp_sq_of_memLp_four (memLp_coord_four s))]
  simp only [Pi.pow_apply, ← pow_mul]
  rw [integral_coord_pow, integral_coord_pow]
  norm_num

/-! ### LD scores `±1`

`ℓ_b` on `Fin (b * 2)` repeats the pattern `(1, -1)` `b` times: mean `0`, `S_ℓℓ = M = 2 b`. -/

/-- The LD scores `(1, -1, 1, -1, …)` on `M = b * 2` markers. -/
noncomputable def ellSeq (b : ℕ) : Fin (b * 2) → ℝ := fun i => ![1, -1] (finProdFinEquiv.symm i).2

theorem sum_ellSeq (b : ℕ) : ∑ i, ellSeq b i = 0 := by
  show ∑ i : Fin (b * 2), ![(1 : ℝ), -1] (finProdFinEquiv.symm i).2 = 0
  rw [sum_comp_snd (b := b) (f := ![(1 : ℝ), -1])]
  simp

theorem sampleMean_ellSeq (b : ℕ) : sampleMean (ellSeq b) = 0 := by
  rw [sampleMean_eq_sum_div, sum_ellSeq, zero_div]

/-- `S_ℓℓ = M`, computed from the definitions. -/
theorem sxy_ellSeq (b : ℕ) : sxy (ellSeq b) (ellSeq b) = (b * 2 : ℕ) := by
  rw [sxy, sampleMean_ellSeq]
  simp only [sub_zero]
  rw [show (∑ i : Fin (b * 2), ellSeq b i * ellSeq b i) =
      ∑ i : Fin (b * 2), (fun r : Fin 2 => ![(1 : ℝ), -1] r * ![(1 : ℝ), -1] r)
        (finProdFinEquiv.symm i).2 from rfl,
    sum_comp_snd (b := b) (f := fun r : Fin 2 => ![(1 : ℝ), -1] r * ![(1 : ℝ), -1] r)]
  simp
  norm_num

theorem ellSeq_ne_zero (b : ℕ) (i : Fin (b * 2)) : ellSeq b i ≠ 0 := by
  unfold ellSeq
  generalize (finProdFinEquiv.symm i).2 = r
  fin_cases r <;> simp

/-! ### Test 1: bounded LD, `Var(ĥ²) → 0`

One marker per LD block (`K = 1`), scores `z_j = ω j` independent with `𝔼 z⁴ = 8`, statistics
`χ_j = z_j²` with `Var(χ_j) = 4`, `N = M = 2 b`, LD scores `±1` with `S_ℓℓ = M`. The induced
T161 bound is `Var(ĥ²) ≤ (M / N)² · 1 · 8 / S_ℓℓ = 8 / M`, and `Var(ĥ²) → 0`. -/

/-- The scores of design `b`. -/
def zSeq (b : ℕ) : Fin (b * 2) → (ℕ → ℝ) → ℝ := fun j ω => ω j

/-- The score-level model for design `b`: one marker per block. -/
def scoreModel (b : ℕ) : ScoreBlockModel (coordMeasure ν2) (zSeq b) 1 where
  block j := j
  card_block_le j := Finset.card_le_one.2 fun x hx y hy => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact Fin.ext (hx.trans hy.symm)
  indepFun j k h := iIndepFun_coord.indepFun h
  memLp j := memLp_coord_four j

theorem integral_stat_sq_le (b : ℕ) (j : Fin (b * 2)) :
    ∫ ω, (1 * zSeq b j ω ^ 2) ^ 2 ∂coordMeasure ν2 ≤ 8 := by
  simp only [one_mul, zSeq]
  rw [integral_coord_sq_sq]

/-- The T161 model induced by the score-level model, with `V = 𝔼 z⁴ = 8`. -/
noncomputable def blockModel (b : ℕ) :
    LDBlockModel (coordMeasure ν2) (fun j ω => 1 * zSeq b j ω ^ 2) 1 8 :=
  (scoreModel b).toLDBlockModel 1 (integral_stat_sq_le b)

/-- The estimator `ĥ² = b̂ · M / N` with `N = M = 2 b`. -/
noncomputable def estSeq (b : ℕ) (ω : ℕ → ℝ) : ℝ :=
  olsSlope (ellSeq b) (fun j => 1 * zSeq b j ω ^ 2) * (b * 2 : ℕ) / (b * 2 : ℕ)

/-- Each statistic has variance exactly `4`, computed from the definitions. -/
theorem variance_stat (b : ℕ) (j : Fin (b * 2)) :
    Var[fun ω => 1 * zSeq b j ω ^ 2; coordMeasure ν2] = 4 := by
  simp only [one_mul, zSeq]
  exact variance_coord_sq j

/-- The explicit bound `Var(ĥ²) ≤ 8 / M`. -/
theorem variance_estSeq_le (b : ℕ) :
    Var[estSeq b; coordMeasure ν2] ≤ 8 / (b * 2 : ℕ) := by
  have h := variance_h2Hat_le (μ := coordMeasure ν2) (N := b * 2) (ellSeq b)
    (blockModel b).memLp (blockModel b).sum_abs_covariance_le (est := estSeq b) fun _ => rfl
  rw [sxy_ellSeq] at h
  refine h.trans (le_of_eq ?_)
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    simp
  · have : ((b * 2 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [div_self this]
    push_cast
    ring

/-- The bound `8 / M` tends to `0`, computed directly. -/
theorem tendsto_bound : Tendsto (fun b : ℕ => (8 : ℝ) / (b * 2 : ℕ)) atTop (𝓝 0) := by
  have h : Tendsto (fun b : ℕ => ((b * 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_id.atTop_mul_const' two_pos)
  have h8 := h.inv_tendsto_atTop.const_mul 8
  rw [mul_zero] at h8
  exact h8.congr fun b => by rw [Pi.inv_apply, div_eq_mul_inv]

/-- **`Var(ĥ²) → 0` in the bounded-LD case**, from the explicit bound. -/
theorem tendsto_variance_estSeq :
    Tendsto (fun b => Var[estSeq b; coordMeasure ν2]) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_bound
    (fun _ => variance_nonneg _ _) variance_estSeq_le

/-- The same limit through T161's `tendsto_variance_h2Hat_of_ldBlock`, with the T161 model
supplied by `ScoreBlockModel.toLDBlockModel`. -/
theorem tendsto_variance_estSeq' :
    Tendsto (fun b => Var[estSeq b; coordMeasure ν2]) atTop (𝓝 0) :=
  tendsto_variance_h2Hat_of_ldBlock (N := fun b => b * 2) (M := fun b => b * 2) ellSeq
    blockModel one_pos one_pos (fun b => by rw [sxy_ellSeq, one_mul])
    (fun b => by rw [one_mul]) (tendsto_id.atTop_mul_const' two_pos) fun _ _ => rfl

/-! ### Test 2: unbounded LD, the limit is not claimed

All markers share one score coordinate: `χ_j = ℓ_j · (ω 0)²`, so every pair of statistics is
correlated and the LD block of any model must contain all `M = 2 b` markers. Then `ĥ² = (ω 0)²`
for every `b ≥ 1` and `Var(ĥ²) = 4` does not tend to `0`. No `LDBlockModel` with a fixed block
size `K` exists once `2 b > K`, so the theorems of `LDScoreVarianceLimit` do not apply. -/

/-- The fully linked statistics of design `b`. -/
noncomputable def chiTot (b : ℕ) : Fin (b * 2) → (ℕ → ℝ) → ℝ :=
  fun j ω => ellSeq b j * ω 0 ^ 2

/-- The estimator for the fully linked statistics. -/
noncomputable def estTot (b : ℕ) (ω : ℕ → ℝ) : ℝ :=
  olsSlope (ellSeq b) (fun j => chiTot b j ω) * (b * 2 : ℕ) / (b * 2 : ℕ)

theorem estTot_eq {b : ℕ} (hb : b ≠ 0) : estTot b = fun ω => ω 0 ^ 2 := by
  funext ω
  have hS : sxy (ellSeq b) (ellSeq b) ≠ 0 := by rw [sxy_ellSeq]; positivity
  have hM : ((b * 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have e : (fun j => chiTot b j ω) = fun j => 0 + ω 0 ^ 2 * ellSeq b j := by
    funext j
    show ellSeq b j * ω 0 ^ 2 = 0 + ω 0 ^ 2 * ellSeq b j
    ring
  rw [estTot, e, olsSlope_affine hS, mul_div_assoc, div_self hM, mul_one]

/-- `Var(ĥ²) = 4` for every design with `b ≥ 1`, computed from the definitions. -/
theorem variance_estTot {b : ℕ} (hb : b ≠ 0) : Var[estTot b; coordMeasure ν2] = 4 := by
  rw [estTot_eq hb]
  exact variance_coord_sq 0

/-- `Var(ĥ²)` does not tend to `0` under unbounded LD. -/
theorem not_tendsto_variance_estTot :
    ¬ Tendsto (fun b => Var[estTot b; coordMeasure ν2]) atTop (𝓝 0) := by
  intro h
  have h4 : Tendsto (fun b => Var[estTot b; coordMeasure ν2]) atTop (𝓝 4) :=
    tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun b hb =>
      (variance_estTot hb).symm)
  have := tendsto_nhds_unique h h4
  norm_num at this

/-- Every pair of fully linked statistics has covariance `4 ℓ_j ℓ_k ≠ 0`. -/
theorem covariance_chiTot (b : ℕ) (j k : Fin (b * 2)) :
    cov[chiTot b j, chiTot b k; coordMeasure ν2] = ellSeq b j * ellSeq b k * 4 := by
  show cov[fun ω : ℕ → ℝ => ellSeq b j * ω 0 ^ 2, fun ω : ℕ → ℝ => ellSeq b k * ω 0 ^ 2;
    coordMeasure ν2] = _
  rw [covariance_const_mul_left, covariance_const_mul_right,
    ProbabilityTheory.covariance_self ((measurable_pi_apply 0).pow_const 2).aemeasurable,
    variance_coord_sq]
  ring

/-- **No bounded LD block structure.** Any `LDBlockModel` for the fully linked statistics has
block size at least `M = 2 b`. -/
theorem le_of_ldBlockModel {b K : ℕ} {V : ℝ}
    (B : LDBlockModel (coordMeasure ν2) (chiTot b) K V) : b * 2 ≤ K := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    simp
  set j₀ : Fin (b * 2) := ⟨0, by omega⟩
  have hall : ∀ k, B.block k = B.block j₀ := fun k => by
    by_contra h
    have h0 := (B.indepFun j₀ k (Ne.symm h)).covariance_eq_zero (B.memLp j₀) (B.memLp k)
    rw [covariance_chiTot] at h0
    exact mul_ne_zero (mul_ne_zero (ellSeq_ne_zero b j₀) (ellSeq_ne_zero b k)) four_ne_zero h0
  have hcard := B.card_block_le j₀
  rwa [Finset.filter_true_of_mem fun k _ => hall k, Finset.card_univ, Fintype.card_fin] at hcard

/-- For any fixed block size `K`, the LD-block hypothesis fails once `2 b > K`. -/
theorem isEmpty_ldBlockModel {b K : ℕ} (hK : K < b * 2) (V : ℝ) :
    IsEmpty (LDBlockModel (coordMeasure ν2) (chiTot b) K V) :=
  ⟨fun B => absurd (le_of_ldBlockModel B) (not_le.2 hK)⟩

/-! ### Test 3: infinite fourth moment, the limit is not claimed

On `ℕ` with mass `2^{-(k+1)}` at `k`, the score `z k = √√(2^{k+1})` has `z⁴ = 2^{k+1}`, so
`∫ z⁴ = ∑ 1 = ∞`. The fourth-moment field of `ScoreBlockModel` fails, and so does the `L²`
field of T161's `LDBlockModel` for `χ = z²`. The kurtosis inequality
`∫ (z²)² ≤ κ₄ (∫ z²)²` still holds for every `κ₄ ≥ 0`, but only because Lean's integral of a
non-integrable function is `0`: this is why the model carries the `L⁴` field. -/

/-- The measure with mass `2^{-(k+1)}` at `k`. -/
noncomputable def μH : Measure ℕ :=
  Measure.sum fun k : ℕ => ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ • Measure.dirac k

/-- A score with infinite fourth moment. -/
noncomputable def zH (k : ℕ) : ℝ := √(√((2 : ℝ) ^ (k + 1)))

theorem norm_zH_pow_four (k : ℕ) : ‖zH k‖ ^ 4 = (2 : ℝ) ^ (k + 1) := by
  have h0 : (0 : ℝ) ≤ √((2 : ℝ) ^ (k + 1)) := Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, zH, abs_of_nonneg (Real.sqrt_nonneg _),
    show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt h0, Real.sq_sqrt (by positivity)]

theorem not_integrable_zH_four : ¬ Integrable (fun k => ‖zH k‖ ^ 4) μH := by
  intro h
  have hfin := h.2
  rw [HasFiniteIntegral, μH, lintegral_sum_measure] at hfin
  have hterm : ∀ k : ℕ, ∫⁻ x, ‖‖zH x‖ ^ 4‖ₑ ∂(((2 : ℝ≥0∞) ^ (k + 1))⁻¹ • Measure.dirac k) = 1 :=
    fun k => by
      rw [lintegral_smul_measure, lintegral_dirac, norm_zH_pow_four, smul_eq_mul]
      have e : ‖(2 : ℝ) ^ (k + 1)‖ₑ = (2 : ℝ≥0∞) ^ (k + 1) := by
        rw [enorm_pow]
        have h2 : ‖(2 : ℝ)‖ₑ = 2 := by simpa using Real.enorm_natCast 2
        rw [h2]
      rw [e]
      exact ENNReal.inv_mul_cancel (pow_ne_zero _ two_ne_zero)
        (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  simp only [hterm, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero] at hfin
  exact lt_irrefl _ hfin

/-- The fourth-moment condition fails. -/
theorem not_memLp_zH_four : ¬ MemLp zH 4 μH := fun h =>
  not_integrable_zH_four (MemLp.integrable_norm_pow (p := 4) (by exact_mod_cast h) (by norm_num))

/-- The statistic `χ = z²` is not in `L²`. -/
theorem not_memLp_zH_sq : ¬ MemLp (fun k => zH k ^ 2) 2 μH := by
  intro h
  rw [memLp_two_iff_integrable_sq h.aestronglyMeasurable] at h
  refine not_integrable_zH_four (h.congr (Eventually.of_forall fun k => ?_))
  simp only
  rw [Real.norm_eq_abs, ← sq_abs (zH k)]
  ring

/-- No score-level model exists for a design with this score at some marker. -/
theorem isEmpty_scoreBlockModel {M K : ℕ} {z : Fin M → ℕ → ℝ} (j : Fin M) (hj : z j = zH) :
    IsEmpty (ScoreBlockModel μH z K) :=
  ⟨fun S => not_memLp_zH_four (hj ▸ S.memLp j)⟩

/-- No T161 LD-block model exists for statistics `χ = z²` at some marker. -/
theorem isEmpty_ldBlockModel_zH {M K : ℕ} {V : ℝ} {χ : Fin M → ℕ → ℝ} (j : Fin M)
    (hj : χ j = fun k => zH k ^ 2) : IsEmpty (LDBlockModel μH χ K V) :=
  ⟨fun B => not_memLp_zH_sq (hj ▸ B.memLp j)⟩

/-- The kurtosis inequality holds vacuously: `∫ (z²)² = 0` by Lean's convention for a
non-integrable function. -/
theorem integral_zH_sq_sq : ∫ k, (zH k ^ 2) ^ 2 ∂μH = 0 := by
  refine integral_undef fun h => not_integrable_zH_four (h.congr (Eventually.of_forall fun k => ?_))
  simp only
  rw [Real.norm_eq_abs, ← sq_abs (zH k)]
  ring

theorem kurtosis_vacuous {κ₄ : ℝ} (hκ₄ : 0 ≤ κ₄) :
    ∫ k, (zH k ^ 2) ^ 2 ∂μH ≤ κ₄ * (∫ k, zH k ^ 2 ∂μH) ^ 2 := by
  rw [integral_zH_sq_sq]
  positivity

/-! ### Test 4: the LD-score regression theorems are not vacuous

On T206's block designs (`LDScoreDesignSequence`: i.i.d. coordinates with a centred,
unit-variance law supported in `[-C, C]`, effects and noise of `model`, genotypes supported on
the cohort of each block), with `h² < 1`, every hypothesis of
`tendstoInMeasure_olsH2Hat_of_fourthMoment` is discharged:

* the scores `β̂_j` of different blocks are independent and bounded, hence in `L⁴`;
* the kurtosis bound holds with `κ₄ = B / (1 - h²)`, where `B = chiSqBound K G C λ` bounds the
  statistics, because `𝔼[χ²] ≤ B 𝔼 χ` and `𝔼 χ ≥ 1 - h²`;
* the LD scores are at most the block size `K`;
* there is no confounding (`s = 0`, `c = 0`, `A = 0`). -/

section BlockDesign

variable {ν : Measure ℝ} [IsProbabilityMeasure ν] {C : ℝ} (hν : IsBoundedUnitLaw ν C) {h2 : ℝ}
  (h0 : 0 ≤ h2) (h1 : h2 ≤ 1)

/-- The score of marker `j` without stratification, written out. -/
theorem betaHatStrat_model {N M : ℕ} (X : Matrix (Fin N) (Fin M) ℝ) (j : Fin M) (ω : ℕ → ℝ) :
    betaHatStrat (model hν h0 h1 N M) X 0 0 j ω =
      (∑ i, X i j * (∑ k, X i k * (√(h2 / M) * ω (2 * k)) +
        √(1 - h2) * ω (2 * i + 1))) / N := by
  simp only [betaHatStrat, phenoStrat, Model.pheno, model, zero_mul, add_zero]

variable {N M K G : ℕ} (D : BlockDesign N M K G)

/-- The score of marker `j` depends only on the coordinates of its block. -/
theorem measurable_betaHatStrat_blockSigma (j : Fin M) :
    Measurable[blockSigma D (D.block j)] (betaHatStrat (model hν h0 h1 N M) D.X 0 0 j) := by
  rw [funext (betaHatStrat_model hν h0 h1 D.X j)]
  refine Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _
  by_cases hij : D.X i j = 0
  · simp only [hij, zero_mul]
    exact measurable_const
  have hg := D.support i j hij
  refine Measurable.const_mul (Measurable.add (Finset.measurable_sum _ fun k _ => ?_) ?_) _
  · by_cases hik : D.X i k = 0
    · simp only [hik, zero_mul]
      exact measurable_const
    · have hk : D.block k = D.block j := (D.support i k hik).symm.trans hg
      exact ((measurable_coord_blockSigma D (Or.inl ⟨k, hk, rfl⟩)).const_mul _).const_mul _
  · exact (measurable_coord_blockSigma D (Or.inr ⟨i, hg, rfl⟩)).const_mul _

theorem measurable_betaHatStrat (j : Fin M) :
    Measurable (betaHatStrat (model hν h0 h1 N M) D.X 0 0 j) :=
  (measurable_betaHatStrat_blockSigma hν h0 h1 D j).mono
    (iSup₂_le fun s _ => (measurable_pi_apply s).comap_le) le_rfl

/-- Scores of different blocks are independent. -/
theorem indepFun_betaHatStrat {j k : Fin M} (h : D.block j ≠ D.block k) :
    IndepFun (betaHatStrat (model hν h0 h1 N M) D.X 0 0 j)
      (betaHatStrat (model hν h0 h1 N M) D.X 0 0 k) (coordMeasure ν) := by
  rw [IndepFun_iff_Indep]
  have hind := indep_iSup_of_disjoint
    (m := fun s => MeasurableSpace.comap (fun ω : ℕ → ℝ => ω s) inferInstance)
    (fun s => (measurable_pi_apply s).comap_le)
    ((iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_coord (ν := ν))) (disjoint_coordSet D h)
  exact indep_of_indep_of_le hind
    (measurable_iff_comap_le.1 (measurable_betaHatStrat_blockSigma hν h0 h1 D j))
    (measurable_iff_comap_le.1 (measurable_betaHatStrat_blockSigma hν h0 h1 D k))

variable {lam : ℝ} (hlam : 0 ≤ lam) (hNM : (N : ℝ) ≤ lam * M)

include hlam hNM in
/-- The scores are bounded by `√B`, hence in `L⁴`. -/
theorem memLp_betaHatStrat (hN : N ≠ 0) (j : Fin M) :
    MemLp (betaHatStrat (model hν h0 h1 N M) D.X 0 0 j) 4 (coordMeasure ν) := by
  refine MemLp.of_bound (measurable_betaHatStrat hν h0 h1 D j).aestronglyMeasurable
    (√(chiSqBound K G C lam)) ((ae_abs_coord_le hν).mono fun ω hω => ?_)
  have h := chiSqStrat_mem_Icc D h0 h1 hlam hNM hν hω j
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN
  have hsq : betaHatStrat (model hν h0 h1 N M) D.X 0 0 j ω ^ 2 ≤ chiSqBound K G C lam := by
    have e : chiSqStrat (model hν h0 h1 N M) D.X 0 0 j ω =
        N * betaHatStrat (model hν h0 h1 N M) D.X 0 0 j ω ^ 2 := rfl
    have := h.2
    rw [e] at this
    nlinarith [sq_nonneg (betaHatStrat (model hν h0 h1 N M) D.X 0 0 j ω)]
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt hsq

include hlam hNM in
/-- The score-level model on a block design. -/
noncomputable def scoreModel_blockDesign (hN : N ≠ 0) :
    ScoreBlockModel (coordMeasure ν) (betaHatStrat (model hν h0 h1 N M) D.X 0 0) K where
  block := D.block
  card_block_le j := D.card_block_le (D.block j)
  indepFun _ _ h := indepFun_betaHatStrat hν h0 h1 D h
  memLp j := memLp_betaHatStrat hν h0 h1 D hlam hNM hN j

include hlam hNM in
/-- **The kurtosis bound on a block design**, with `κ₄ = B / (1 - h²)`. -/
theorem kurtosis_blockDesign (hN : N ≠ 0) (hh2 : h2 < 1) (j : Fin M) :
    ∫ ω, chiSqStrat (model hν h0 h1 N M) D.X 0 0 j ω ^ 2 ∂coordMeasure ν ≤
      chiSqBound K G C lam / (1 - h2) *
        (∫ ω, chiSqStrat (model hν h0 h1 N M) D.X 0 0 j ω ∂coordMeasure ν) ^ 2 := by
  set B := chiSqBound K G C lam
  set χ := chiSqStrat (model hν h0 h1 N M) D.X 0 0 j
  have hB : 0 ≤ B := by
    have hC : 0 ≤ 2 * C ^ 2 * (K ^ 2 * lam + 1) := by positivity
    exact mul_nonneg G.cast_nonneg hC
  have hpos : 0 < 1 - h2 := sub_pos.2 hh2
  -- `𝔼 χ ≥ 1 - h²`
  have he : 1 - h2 ≤ ∫ ω, χ ω ∂coordMeasure ν := by
    rw [integral_chiSqStrat_eq (model hν h0 h1 N M) D.X hN D.isStandardized
      (integral_model_beta hν h0 h1) (integral_model_eps hν h0 h1) 0 0 (a := 0)
      (fun _ => by simp) j, model_h2]
    have hℓ := D.isStandardized.one_le_ldScore hN j
    have : 0 ≤ (N : ℝ) * h2 * ldScore D.X j / M := by positivity
    linarith
  -- `𝔼[χ²] ≤ B 𝔼 χ`
  have hle : ∫ ω, χ ω ^ 2 ∂coordMeasure ν ≤ ∫ ω, B * χ ω ∂coordMeasure ν := by
    refine integral_mono_ae ((ldBlockModel D hν h0 h1 hlam hNM).memLp j).integrable_sq
      ((integrable_chiSqStrat _ _ _ _ j).const_mul B) ((ae_abs_coord_le hν).mono fun ω hω => ?_)
    have h := chiSqStrat_mem_Icc D h0 h1 hlam hNM hν hω j
    have : χ ω * χ ω ≤ B * χ ω := mul_le_mul_of_nonneg_right h.2 h.1
    simpa [sq] using this
  rw [integral_const_mul] at hle
  refine hle.trans ?_
  set e := ∫ ω, χ ω ∂coordMeasure ν
  have he0 : 0 ≤ e := hpos.le.trans he
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith [mul_nonneg hB (mul_nonneg he0 (sub_nonneg.2 he))]

/-- On a block design, every LD score is at most the block size `K`. -/
theorem ldScore_le_blockSize (j : Fin M) : ldScore D.X j ≤ K := by
  calc ldScore D.X j = ∑ k, ldCorr D.X j k ^ 2 := rfl
    _ ≤ ∑ k, if D.block k = D.block j then (1 : ℝ) else 0 := sum_le_sum fun k _ => by
        split_ifs with h
        · exact D.isStandardized.ldCorr_sq_le_one j k
        · rw [D.ldCorr_eq_zero fun h' => h h'.symm]
          simp
    _ = #{k | D.block k = D.block j} := by rw [← sum_filter, sum_const, nsmul_one]
    _ ≤ K := by exact_mod_cast D.card_block_le (D.block j)

end BlockDesign

section Sequence

variable {ν : Measure ℝ} [IsProbabilityMeasure ν] {C : ℝ} (hν : IsBoundedUnitLaw ν C) {h2 : ℝ}
  (h0 : 0 ≤ h2) (h1 : h2 ≤ 1)

/-- **Non-vacuity of `tendstoInMeasure_olsH2Hat_of_fourthMoment`.** Along T206's block designs
with `M → ∞` (every `M n ≠ 0`), `κ M ≤ N ≤ λ M` (`κ > 0`), LD-score spread `S_ℓℓ ≥ c₀ M`
(`c₀ > 0`) and `h² < 1`, the fourth-moment theorem applies with every model hypothesis
discharged, and gives `ĥ² → h²` in probability. -/
theorem tendstoInMeasure_blockDesign_of_fourthMoment {ι : Type*} {l : Filter ι}
    {N M : ι → ℕ} {K G : ℕ} (D : ∀ n, BlockDesign (N n) (M n) K G) (hh2 : h2 < 1)
    {κ lam c₀ : ℝ} (hκ : 0 < κ) (hNM : ∀ n, κ * M n ≤ N n) (hNM' : ∀ n, (N n : ℝ) ≤ lam * M n)
    (hc₀ : 0 < c₀) (hspread : ∀ n, c₀ * M n ≤ sxy (ldScore (D n).X) (ldScore (D n).X))
    (hM : Tendsto M l atTop) (hM0 : ∀ n, M n ≠ 0) :
    TendstoInMeasure (coordMeasure ν) (fun n ω => olsH2Hat (N n) (M n) (ldScore (D n).X)
      fun j => chiSqStrat (model hν h0 h1 (N n) (M n)) (D n).X 0 0 j ω) l fun _ => h2 := by
  have hMr : ∀ n, (0 : ℝ) < M n := fun n => by exact_mod_cast Nat.pos_of_ne_zero (hM0 n)
  have hN : ∀ n, N n ≠ 0 := fun n => by
    have h := (mul_pos hκ (hMr n)).trans_le (hNM n)
    exact_mod_cast h.ne'
  have hlam : 0 ≤ max lam 0 := le_max_right _ _
  have hκ₄ : 0 ≤ chiSqBound K G C (max lam 0) / (1 - h2) := by
    have hC : 0 ≤ 2 * C ^ 2 * (K ^ 2 * max lam 0 + 1) := by positivity
    exact div_nonneg (mul_nonneg G.cast_nonneg hC) (sub_pos.2 hh2).le
  exact tendstoInMeasure_olsH2Hat_of_fourthMoment (fun n => model hν h0 h1 (N n) (M n))
    (fun n => (D n).X) (fun _ => rfl) hN hM0 (fun n => (D n).isStandardized)
    (fun _ => integral_model_beta hν h0 h1) (fun _ => integral_model_eps hν h0 h1) (fun _ => 0)
    (fun n => (0 : Fin (N n) → ℝ)) (fun _ => 0) (fun _ _ => by simp)
    (fun n => scoreModel_blockDesign hν h0 h1 (D n) hlam (le_max_mul hNM' n) (hN n)) hκ₄
    (fun n j => kurtosis_blockDesign hν h0 h1 (D n) hlam (le_max_mul hNM' n) (hN n) hh2 j)
    (fun n j => ldScore_le_blockSize (D n) j) (fun n => le_max_mul hNM' n)
    (A := 0) (fun _ => (mul_zero _).le) hc₀ hκ hspread hNM hM

end Sequence

end MathlibExtTest.Biology.StatisticalGenetics.LDScoreVarianceLimit
