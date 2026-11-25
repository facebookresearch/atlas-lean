/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import MathlibExt.Probability.Distributions.GaussianL2Limit
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Series of independent centered Gaussians

If `X k ~ 𝓝(0, v k)` are independent and `∑ v k < ∞`, then the partial sums `∑_{k < n} X k`
converge in `L²` to a random variable `S ~ 𝓝(0, ∑' k, v k)`
(`ProbabilityTheory.iIndepFun.exists_tendsto_eLpNorm_sum_hasLaw_gaussianReal`).

The variance of a block `∑_{n ≤ k < m} X k` is `∑_{n ≤ k < m} v k`, so the partial sums are
Cauchy in `L²`. Each partial sum is `𝓝(0, ∑_{k < n} v k)` (`iIndepFun.hasGaussianLaw_fun_sum`
plus mean and variance). Gaussian laws are closed under `L²` limits
(`HasGaussianLaw.of_tendsto_eLpNorm_real`), and the mean and the second moment pass to the
`L²` limit (`tendsto_integral_of_L1'`, `tendsto_integral_mul_of_tendsto_eLpNorm`), so the limit
is `𝓝(0, ∑' k, v k)`.

Mathlib has finite sums of independent Gaussians (`iIndepFun.hasGaussianLaw_sum`,
`gaussianReal_add_gaussianReal_of_indepFun`) but not the series.

Code-derived port of `SumIndependentGaussians.sum_independent_gaussians` and its helpers from
`v1/Atlas/FourierAnalysis/code/BrownianMotion.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 2054–2385 (Proposition 1 of Chapter 1,
Brownian Motion). The archived wrappers `hasGaussianLaw_of_hasLaw` and `memLp_two_of_hasLaw`
are inlined as `HasLaw.hasGaussianLaw` and `HasGaussianLaw.memLp_two`, `variance_of_hasLaw` and
`integral_eq_zero_of_hasLaw` are kept with one-line proofs from `HasLaw.variance_eq` and
`HasLaw.integral_eq`, and the heartbeat overrides are dropped. The law of the limit is
identified with ATLAS's `HasGaussianLaw.of_tendsto_eLpNorm_real` instead of the archived argument
through convergence in distribution and Lévy's continuity theorem. The archived formalization and
its original license/provenance remain in `v1/` (the original license text is `v1/LICENSE`). This
records equivalence to the archived Lean statement, not verification against the printed
textbook.
-/

set_option autoImplicit false

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- If `X ~ 𝓝(0, v)` under `P`, then `Var[X; P] = v`. -/
lemma variance_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hlaw : HasLaw X (gaussianReal 0 v) P) :
    Var[X; P] = ↑v :=
  hlaw.variance_eq.trans variance_id_gaussianReal

/-- If `X ~ 𝓝(0, v)` under `P`, then `𝔼[X] = 0`. -/
lemma integral_eq_zero_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hlaw : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω ∂P = 0 :=
  hlaw.integral_eq.trans integral_id_gaussianReal

/-- The partial sum `∑_{k < n} X k` of Gaussian random variables lies in `L²(P)`. -/
lemma memLp_partialSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P) (n : ℕ) :
    MemLp (fun ω => ∑ k ∈ range n, X k ω) 2 P :=
  memLp_finsetSum _ (fun k _ => (hgauss k).hasGaussianLaw.memLp_two)

/-- The partial sum `∑_{k < n} X k` as an element of `L²(P)`. -/
noncomputable def partialSumLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P) (n : ℕ) :
    Lp ℝ 2 P :=
  (memLp_partialSum hgauss n).toLp _

/-- For a centered `L²` random variable `f` on a probability space, `‖f‖₂² = Var[f]`. -/
lemma eLpNorm_sq_eq_variance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : MemLp f 2 P) (hm : ∫ ω, f ω ∂P = 0) :
    (eLpNorm f 2 P).toReal ^ 2 = variance f P := by
  rw [variance_eq_sub hf, hm]
  simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_zero]
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)]
  simp only [ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
  norm_num

/-- For independent `X k ~ 𝓝(0, v k)`, the block sum `∑_{n ≤ k < m} X k` has variance
`∑_{n ≤ k < m} v k`. -/
lemma variance_icoSum_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P) (n m : ℕ) :
    variance (fun ω => ∑ k ∈ Ico n m, X k ω) P = ∑ k ∈ Ico n m, (v k : ℝ) := by
  have hf : (fun ω => ∑ k ∈ Ico n m, X k ω) = ∑ k ∈ Ico n m, X k := by
    ext ω; simp [Finset.sum_apply]
  rw [hf, IndepFun.variance_sum
    (fun k _ => (hgauss k).hasGaussianLaw.memLp_two)
    (fun i _ j _ hij => hindep.indepFun hij)]
  exact Finset.sum_congr rfl (fun k _ => variance_of_hasLaw (hgauss k))

/-- For a summable nonnegative `v`, a block sum is at most the tail of the series:
`∑_{n ≤ k < m} v k ≤ ∑' k, v (k + n)`. -/
lemma sum_Ico_le_tsum_tail (v : ℕ → ℝ≥0) (hsum : Summable v) (n m : ℕ) :
    ∑ k ∈ Ico n m, (v k : ℝ) ≤ ∑' k, (v (k + n) : ℝ) := by
  have hsv : Summable (fun k => v (k + n)) := NNReal.summable_nat_add v hsum n
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [show ∀ k, v (n + k) = v (k + n) from fun k => by rw [add_comm]]
  have : ∀ i ∉ Finset.range (m - n), (0 : ℝ) ≤ (v (i + n) : ℝ) := fun i _ => NNReal.coe_nonneg _
  exact sum_le_hasSum _ this (NNReal.summable_coe.mpr hsv).hasSum

/-- For `n ≤ m`, the `L²` distance between the partial sums up to `n` and `m` is at most
`√(∑' k, v (k + n))`, the square root of the tail of the variance series. -/
lemma dist_partialSumLp_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hsum : Summable v) {n m : ℕ} (hnm : n ≤ m) :
    dist (partialSumLp hgauss n) (partialSumLp hgauss m) ≤
      Real.sqrt (∑' k, (v (k + n) : ℝ)) := by
  rw [dist_comm, Lp.dist_def]
  set f := fun ω => ∑ k ∈ Ico n m, X k ω
  have hae : (↑↑(partialSumLp hgauss m) - ↑↑(partialSumLp hgauss n) : Ω → ℝ) =ᵐ[P] f := by
    simp only [partialSumLp]
    filter_upwards [(memLp_partialSum hgauss n).coeFn_toLp,
      (memLp_partialSum hgauss m).coeFn_toLp] with ω hωn hωm
    simp only [Pi.sub_apply, hωm, hωn, f, ← sum_sdiff_eq_sub (range_mono hnm)]
    congr 1
    ext k; simp only [Finset.mem_sdiff, mem_range, mem_Ico, not_lt]; omega
  rw [eLpNorm_congr_ae hae]
  have hf_lp : MemLp f 2 P :=
    memLp_finsetSum _ (fun k _ => (hgauss k).hasGaussianLaw.memLp_two)
  have hf_mean : ∫ ω, f ω ∂P = 0 := by
    change ∫ ω, ∑ k ∈ Ico n m, X k ω ∂P = 0
    rw [integral_finsetSum _ (fun k _ =>
      ((hgauss k).hasGaussianLaw.memLp_two).integrable (by norm_num))]
    exact Finset.sum_eq_zero (fun k _ => integral_eq_zero_of_hasLaw (hgauss k))
  have h_sq_le : (eLpNorm f 2 P).toReal ^ 2 ≤ ∑' k, (v (k + n) : ℝ) := by
    rw [eLpNorm_sq_eq_variance hf_lp hf_mean, variance_icoSum_eq hindep hgauss n m]
    exact sum_Ico_le_tsum_tail v hsum n m
  calc (eLpNorm f 2 P).toReal
      = Real.sqrt ((eLpNorm f 2 P).toReal ^ 2) := (Real.sqrt_sq ENNReal.toReal_nonneg).symm
    _ ≤ Real.sqrt (∑' k, (v (k + n) : ℝ)) := Real.sqrt_le_sqrt h_sq_le

/-- If `∑ v k < ∞`, the partial sums `∑_{k < n} X k` are Cauchy in `L²(P)`. -/
theorem cauchySeq_partialSumLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hsum : Summable v) :
    CauchySeq (partialSumLp hgauss) := by
  apply cauchySeq_of_le_tendsto_0' (fun N => Real.sqrt (∑' k, (v (k + N) : ℝ)))
  · intro n m hnm
    exact dist_partialSumLp_le hindep hgauss hsum hnm
  · rw [show (0 : ℝ) = Real.sqrt 0 from Real.sqrt_zero.symm]
    exact (Real.continuous_sqrt.tendsto 0).comp (tendsto_sum_nat_add (fun k => (v k : ℝ)))

/-- By completeness of `L²(P)`, the partial sums `∑_{k < n} X k` converge in `L²(P)` to some
`S ∈ L²(P)`. -/
theorem exists_L2_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hsum : Summable v) :
    ∃ S : Ω → ℝ, MemLp S 2 P ∧
      Tendsto (fun n => eLpNorm (fun ω => (∑ k ∈ range n, X k ω) - S ω) 2 P)
        atTop (nhds 0) := by
  have hcauchy := cauchySeq_partialSumLp X v hindep hgauss hsum
  have hfact : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  set S := (L : Ω → ℝ)
  have hS_mem : MemLp S 2 P := Lp.memLp L
  refine ⟨S, hS_mem, ?_⟩
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hL
  refine hL.congr (fun n => ?_)
  apply eLpNorm_congr_ae
  have h1 := (memLp_partialSum hgauss n).coeFn_toLp
  filter_upwards [h1] with ω hω
  simp only [partialSumLp, Pi.sub_apply]
  rw [hω]

/-- A partial sum of independent Gaussian random variables has a Gaussian law. -/
theorem hasGaussianLaw_partialSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (n : ℕ) :
    HasGaussianLaw (fun ω => ∑ k ∈ range n, X k ω) P := by
  have hindep_n : iIndepFun ((range n).restrict X) P :=
    iIndepFun_iff_finset.mp hindep (range n)
  have hgauss_n : ∀ i : ↥(range n), HasGaussianLaw (((range n).restrict X) i) P :=
    fun i => (hgauss i.val).hasGaussianLaw
  have hG := iIndepFun.hasGaussianLaw_fun_sum hgauss_n hindep_n
  have heq : (fun ω => ∑ i, ((range n).restrict X) i ω) =
      (fun ω => ∑ k ∈ range n, X k ω) := by
    ext ω
    simp only [Finset.restrict]
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach (range n) (fun k => X k ω)
  rwa [heq] at hG

/-- For independent `X k ~ 𝓝(0, v k)`, `∑_{k < n} X k ~ 𝓝(0, ∑_{k < n} v k)`. -/
lemma hasLaw_partialSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (n : ℕ) :
    HasLaw (fun ω => ∑ k ∈ range n, X k ω) (gaussianReal 0 (∑ k ∈ range n, v k)) P := by
  have hG := hasGaussianLaw_partialSum X v hindep hgauss n
  have hIsG : IsGaussian (P.map (fun ω => ∑ k ∈ range n, X k ω)) := hG.isGaussian_map
  have hmean : ∫ ω, (∑ k ∈ range n, X k ω) ∂P = 0 := by
    rw [integral_finsetSum _ fun k _ =>
      ((hgauss k).hasGaussianLaw.memLp_two).integrable one_le_two]
    simp only [integral_eq_zero_of_hasLaw (hgauss _), Finset.sum_const_zero]
  constructor
  · exact hG.aemeasurable
  · have h1 := hIsG.eq_gaussianReal (P.map (fun ω => ∑ k ∈ range n, X k ω))
    rw [h1]
    congr 1
    · rw [integral_map hG.aemeasurable aestronglyMeasurable_id]
      simp only [id]
      exact hmean
    · rw [variance_map aemeasurable_id hG.aemeasurable, Function.id_comp]
      rw [show (fun ω => ∑ k ∈ range n, X k ω) = (∑ k ∈ range n, X k) from
        funext (fun ω => (Finset.sum_apply ω (range n) X).symm)]
      rw [IndepFun.variance_sum
        (fun k _ => (hgauss k).hasGaussianLaw.memLp_two)
        (fun i hi j hj hij => hindep.indepFun hij)]
      simp only [variance_of_hasLaw (hgauss _)]
      simp only [← NNReal.coe_sum]
      exact Real.toNNReal_coe

/-- An `L²` limit `S` of the partial sums has law `𝓝(0, ∑' k, v k)`. It is Gaussian because
Gaussian laws are closed under `L²` limits (`HasGaussianLaw.of_tendsto_eLpNorm_real`), and its mean
and variance are the limits of those of the partial sums, `0` and `∑_{k < n} v k → ∑' k, v k`. -/
theorem hasLaw_of_L2_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hsum : Summable v)
    (S : Ω → ℝ) (hS_mem : MemLp S 2 P)
    (hS_lim : Tendsto (fun n => eLpNorm (fun ω => (∑ k ∈ range n, X k ω) - S ω) 2 P)
        atTop (nhds 0)) :
    HasLaw S (gaussianReal 0 (∑' k, v k)) P := by
  have hSn : ∀ n, MemLp (fun ω => ∑ k ∈ range n, X k ω) 2 P := memLp_partialSum hgauss
  have hlim : Tendsto (fun n => eLpNorm ((fun ω => ∑ k ∈ range n, X k ω) - S) 2 P)
      atTop (nhds 0) := hS_lim
  have hG : HasGaussianLaw S P :=
    HasGaussianLaw.of_tendsto_eLpNorm_real (hasGaussianLaw_partialSum X v hindep hgauss)
      hS_mem.aestronglyMeasurable hlim
  have hlaw_n := hasLaw_partialSum X v hindep hgauss
  -- The means of the partial sums, all `0`, converge to the mean of `S`.
  have hmean : ∫ ω, S ω ∂P = 0 := by
    have h : Tendsto (fun n => ∫ ω, ∑ k ∈ range n, X k ω ∂P) atTop
        (nhds (∫ ω, S ω ∂P)) := by
      refine tendsto_integral_of_L1' S
        (Eventually.of_forall fun n => (hSn n).integrable one_le_two) ?_
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun _ => zero_le) (fun _ => eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
    simp only [fun n => integral_eq_zero_of_hasLaw (hlaw_n n)] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  -- The second moments of the partial sums, `∑_{k < n} v k`, converge to that of `S`.
  have hvar : Var[S; P] = ∑' k, (v k : ℝ) := by
    have h := tendsto_integral_mul_of_tendsto_eLpNorm hSn hSn hS_mem hS_mem hlim hlim
    have hn : ∀ n, ∫ ω, (∑ k ∈ range n, X k ω) * (∑ k ∈ range n, X k ω) ∂P =
        ∑ k ∈ range n, (v k : ℝ) := by
      intro n
      have h1 := variance_eq_sub (hSn n)
      rw [variance_of_hasLaw (hlaw_n n), integral_eq_zero_of_hasLaw (hlaw_n n)] at h1
      simpa only [Pi.pow_apply, pow_two, NNReal.coe_sum, mul_zero, sub_zero] using h1.symm
    simp only [hn] at h
    rw [variance_eq_sub hS_mem, hmean]
    simpa only [Pi.pow_apply, pow_two, mul_zero, sub_zero] using
      tendsto_nhds_unique h (NNReal.summable_coe.mpr hsum).hasSum.tendsto_sum_nat
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal, hmean, hvar, ← NNReal.coe_tsum, Real.toNNReal_coe]

/-- A series of independent centered Gaussians `X k ~ 𝓝(0, v k)` with `∑ v k < ∞` converges in
`L²` to a random variable with law `𝓝(0, ∑' k, v k)`. -/
public theorem iIndepFun.exists_tendsto_eLpNorm_sum_hasLaw_gaussianReal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P) (hsum : Summable v) :
    ∃ S : Ω → ℝ,
      Tendsto (fun n => eLpNorm (fun ω => S ω - ∑ k ∈ range n, X k ω) 2 P) atTop (nhds 0) ∧
      HasLaw S (gaussianReal 0 (∑' k, v k)) P := by
  obtain ⟨S, hS_mem, hS_lim⟩ := exists_L2_limit X v hindep hgauss hsum
  refine ⟨S, ?_, hasLaw_of_L2_limit X v hindep hgauss hsum S hS_mem hS_lim⟩
  have hsymm : ∀ n, eLpNorm (fun ω => S ω - ∑ k ∈ range n, X k ω) 2 P =
      eLpNorm (fun ω => (∑ k ∈ range n, X k ω) - S ω) 2 P := fun n => by
    simp_rw [show ∀ ω, S ω - ∑ k ∈ range n, X k ω =
      -(((∑ k ∈ range n, X k ω) - S ω)) from fun ω => by ring]
    exact eLpNorm_neg ..
  simp_rw [hsymm]
  exact hS_lim

end ProbabilityTheory
