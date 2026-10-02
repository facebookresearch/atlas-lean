/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# CDIS Probabilités IV: bridge statements (V3 sample)

* id 62: Markov's inequality `P(|X| ≥ a) ≤ E(|X|^p) / a^p`. The course states it for `a ∈ ℝ*`,
  which is false for `a < 0` (see `not_markov_of_neg`); the correct hypothesis is `a > 0`.
* id 63: the course's Chebyshev inequality does not quantify `a`; `not_chebyshev_of_neg`
  shows it fails for `a < 0`.
* id 74: strong law of large numbers, almost sure and `L¹` convergence.
* id 79: central limit theorem in the course's normalisation `(S_n - n m) / (σ √n) → N(0,1)`.
* id 89: characteristic function of a Gaussian vector, with mean vector and covariance.
* id 90: Lévy's continuity theorem, both directions of the course statement.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal RealInnerProductSpace

namespace CDIS

section Markov

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- CDIS P.IV, id 62 (Markov's inequality), with the corrected hypothesis `0 < a`. -/
theorem markov_abs_pow {X : Ω → ℝ} {p : ℕ} (hp : p ≠ 0) {a : ℝ} (ha : 0 < a)
    (hX : MemLp X p P) :
    P.real {ω | a ≤ |X ω|} ≤ (∫ ω, |X ω| ^ p ∂P) / a ^ p := by
  have hint : Integrable (fun ω ↦ |X ω| ^ p) P := by
    simpa [Real.norm_eq_abs] using hX.integrable_norm_pow hp
  have hset : {ω | a ≤ |X ω|} = {ω | a ^ p ≤ |X ω| ^ p} := by
    ext ω
    exact (pow_le_pow_iff_left₀ ha.le (abs_nonneg _) hp).symm
  have key := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω ↦ by positivity) hint (a ^ p)
  rw [hset, le_div_iff₀ (by positivity), mul_comm]
  exact key

/-- The course's literal statement of id 62 (with `a ∈ ℝ*`) is false: take `p = 1`, `a = -1`,
`X = 0`. The left side is `1` and the right side is `0`. -/
theorem not_markov_of_neg :
    ¬ ∀ (p : ℕ) (a : ℝ) (X : Ω → ℝ), 1 ≤ p → a ≠ 0 → MemLp X p P →
      P.real {ω | a ≤ |X ω|} ≤ (∫ ω, |X ω| ^ p ∂P) / a ^ p := by
  intro h
  have := h 1 (-1) (fun _ ↦ 0) le_rfl (by norm_num) (memLp_const 0)
  norm_num at this

/-- CDIS P.IV, id 63: the course states Bienaymé-Chebyshev `P(|X - E X| > a) ≤ Var(X) / a²`
without quantifying `a`; it is false for `a < 0` (take `X = 0`, `a = -1`). -/
theorem not_chebyshev_of_neg :
    ¬ ∀ (a : ℝ) (X : Ω → ℝ), MemLp X 2 P →
      P.real {ω | a < |X ω - ∫ ω', X ω' ∂P|} ≤ Var[X; P] / a ^ 2 := by
  intro h
  have := h (-1) 0 (memLp_const 0)
  norm_num [variance_zero] at this

end Markov

section LLN

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- CDIS P.IV, id 74 (law of large numbers, `L¹` case): for i.i.d. integrable `X n`, the
empirical mean `M_n` converges to `m = E(X₀)` almost surely and in `L¹`. -/
theorem lln_ae_and_L1 {X : ℕ → Ω → ℝ} (hint : Integrable (X 0) P) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    (∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (∑ i ∈ range n, X i ω) / n) atTop (𝓝 (∫ ω, X 0 ω ∂P))) ∧
      Tendsto (fun n : ℕ ↦ eLpNorm (fun ω ↦ (∑ i ∈ range n, X i ω) / n - ∫ ω, X 0 ω ∂P) 1 P)
        atTop (𝓝 0) := by
  have hpair : Pairwise (Function.onFun (· ⟂ᵢ[P] ·) X) := fun i j hij ↦ hindep.indepFun hij
  refine ⟨strong_law_ae_real X hint hpair hident, ?_⟩
  have := strong_law_Lp le_rfl ENNReal.one_ne_top X (memLp_one_iff_integrable.2 hint) hpair hident
  simpa [smul_eq_mul, inv_mul_eq_div] using this

end LLN

section CLT

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- CDIS P.IV, id 79 (central limit theorem): for i.i.d. square-integrable `X n` with mean `m`
and variance `σ² > 0`, `(S_n - n m) / (σ √n)` converges in law to `N(0, 1)`. -/
theorem clt_standardized {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P')
    (h2 : MemLp (X 0) 2 P) (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hσ : 0 < Var[X 0; P]) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (∑ k ∈ range n, X k ω - n * ∫ ω, X 0 ω ∂P) / (√(Var[X 0; P]) * √n))
      atTop Z (fun _ ↦ P) P' := by
  set σ := √(Var[X 0; P]) with hσdef
  have hσ0 : σ ≠ 0 := (Real.sqrt_pos.2 hσ).ne'
  -- `σ Z` has law `N(0, σ²)`, the limit given by Mathlib's central limit theorem.
  have hY : HasLaw (fun ω ↦ σ * Z ω) (gaussianReal 0 (Var[X 0; P]).toNNReal) P' := by
    refine ⟨(measurable_const_mul σ).comp_aemeasurable hZ.aemeasurable, ?_⟩
    rw [show (fun ω ↦ σ * Z ω) = (fun x ↦ σ * x) ∘ Z from rfl,
      ← AEMeasurable.map_map_of_aemeasurable (measurable_const_mul σ).aemeasurable
      hZ.aemeasurable, hZ.map_eq, gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [hσdef, Real.sq_sqrt hσ.le, hσ.le]
  have h := (tendstoInDistribution_inv_sqrt_mul_sum_sub hY h2 hindep hident).continuous_comp
    (continuous_const_mul σ⁻¹)
  convert h using 2 with n
  · ext ω
    simp only [Function.comp_apply]
    rw [div_eq_mul_inv, mul_inv]
    ring
  · ext ω
    simp [hσ0]

end CLT

section Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- CDIS P.IV, id 89: a square-integrable law `μ` on a Euclidean space is Gaussian iff
`φ(u) = exp(i ⟪u, m⟫ - ⟪u, C u⟫ / 2)`, with `m = E(X)` and `C` the covariance (as a bilinear
form; `covarianceBilin_self_nonneg` gives that it is positive semidefinite). -/
theorem isGaussian_iff_charFun_eq_mean_cov {μ : Measure E} [IsProbabilityMeasure μ]
    (h2 : MemLp id 2 μ) :
    IsGaussian μ ↔ ∀ u : E,
      charFun μ u = Complex.exp (⟪u, ∫ x, x ∂μ⟫ * Complex.I - covarianceBilin μ u u / 2) := by
  rw [isGaussian_iff_charFun_eq]
  have hint : Integrable id μ := h2.integrable one_le_two
  refine forall_congr' fun u ↦ ?_
  have hi : ∫ x, ⟪u, x⟫ ∂μ = ⟪u, ∫ x, x ∂μ⟫ := integral_inner hint u
  rw [covarianceBilin_self h2, integral_complex_ofReal, hi]

/-- CDIS P.IV, id 90, part 1: convergence in law implies pointwise convergence of the
characteristic functions. -/
theorem tendsto_charFun_of_tendstoInDistribution {Ω' : Type*} {Ω : ℕ → Type*}
    {m : ∀ n, MeasurableSpace (Ω n)} {P : (n : ℕ) → Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {m' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : (n : ℕ) → Ω n → E} {X' : Ω' → E}
    (h : TendstoInDistribution X atTop X' P P') (u : E) :
    Tendsto (fun n ↦ charFun ((P n).map (X n)) u) atTop (𝓝 (charFun (P'.map X') u)) :=
  h.tendsto_charFun u

/-- CDIS P.IV, id 90, part 2 (Lévy's continuity theorem): if the characteristic functions
converge pointwise to a function `φ` continuous at `0`, then `φ` is the characteristic function
of a probability measure `μ₀`, and the sequence converges in law to `μ₀`. -/
theorem exists_tendsto_of_tendsto_charFun {μ : ℕ → ProbabilityMeasure E} {φ : E → ℂ}
    (hφ : ContinuousAt φ 0) (h : ∀ u, Tendsto (fun n ↦ charFun (μ n) u) atTop (𝓝 (φ u))) :
    ∃ μ₀ : ProbabilityMeasure E, charFun (μ₀ : Measure E) = φ ∧ Tendsto μ atTop (𝓝 μ₀) := by
  have h_tight := isTightMeasureSet_of_tendsto_charFun (μ := fun n ↦ (μ n : Measure E)) hφ h
  have h_compact : IsCompact (closure (Set.range μ)) := by
    refine isCompact_closure_of_isTightMeasureSet ?_
    convert h_tight using 1
    ext ν
    simp
  obtain ⟨μ₀, -, ψ, hψ, hlim⟩ := h_compact.tendsto_subseq fun n ↦ subset_closure ⟨n, rfl⟩
  have hφμ₀ : charFun (μ₀ : Measure E) = φ := by
    funext u
    refine tendsto_nhds_unique ?_ ((h u).comp hψ.tendsto_atTop)
    exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hlim u
  refine ⟨μ₀, hφμ₀, ProbabilityMeasure.tendsto_of_tendsto_charFun fun u ↦ ?_⟩
  rw [hφμ₀]
  exact h u

end Gaussian

end CDIS
