/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LindebergFeller
public import Mathlib.Probability.CramerWold
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# GEE asymptotics: root consistency, cluster CLT and the sandwich covariance

Generalized estimating equations (GEE) estimate a parameter `β ∈ E` (a finite-dimensional real
inner product space) from independent clusters by solving `∑_{i<n} U i β = 0`, where
`U i β ω ∈ E` is the score of cluster `i`; for the GEE of Liang and Zeger,
`U i β = D i(β)ᵀ V i(β)⁻¹ (Y i - μ i(β))` with a working covariance `V i`. This file treats an
arbitrary cluster estimating function `U`, so the GEE score is one instance (see the tests).
Unbiasedness of the estimating function at the true parameter, `E[U i β₀] = 0`, is an explicit
hypothesis here rather than imported from a sibling development.

Write `A` for the sensitivity (bread) matrix, the limit of the averaged Jacobians
`n⁻¹ ∑ ∂U i/∂β`, and `B` for the variability (meat) matrix, the limit of the averaged
covariances `n⁻¹ ∑ E[U i β₀ U i β₀ᵀ]`. The asymptotic covariance of the estimator is the
sandwich `A⁻¹ B A⁻ᵀ`.

## Main statements

* (a) `ProbabilityTheory.GEE.tendstoInMeasure_of_tendstoUniformlyOn_of_root`: consistency of a
  root. Hypotheses: uniform convergence in probability of `n⁻¹ • ∑ U i β` to `g β` on a compact
  `K`; identifiability (`g` continuous on `K` with `β₀` its only zero there); and root existence
  in the neighbourhood (`βhat n ∈ K` and `∑ U i (βhat n) = 0`, each with probability tending
  to one). Root existence is an explicit hypothesis; consistency is proved.
* (b) `ProbabilityTheory.GEE.tendstoInDistribution_inv_sqrt_smul_sum_of_lindeberg`: the central
  limit theorem for independent, non-identically distributed clusters, under the projected
  cluster Lindeberg condition (`LindebergConditionTriangular` for `(√n)⁻¹ ⟪U k, t⟫`); the
  limiting meat may be singular. `lindebergConditionTriangular_inner_of_norm` derives the
  projected condition from the classical norm form
  `n⁻¹ ∑ E[‖U k‖² 𝟙{ε √n < ‖U k‖}] → 0`, and
  `lindebergConditionTriangular_inner_of_identDistrib` proves it for identically distributed
  square-integrable clusters.
* (b) `ProbabilityTheory.GEE.tendstoInDistribution_sqrt_smul_sub_of_linearization`: a root that
  linearizes with an invertible derivative `A` inherits the limit law of the cluster sums
  `-A⁻¹ (√n)⁻¹ ∑ U i β₀`. `linearization_of_hasFDerivAt` proves the linearization from
  differentiable scores, uniform convergence of the averaged Jacobian and consistency.
* (b) `ProbabilityTheory.GEE.tendstoInDistribution_sqrt_smul_sub_sandwich`: GEE asymptotic
  normality, `√n (βhat n - β₀) → N(0, A⁻¹ B A⁻ᵀ)`, with sensitivity nonsingularity `IsUnit A`
  as an explicit hypothesis; `tendstoInDistribution_sqrt_smul_sub_sandwich_of_hasFDerivAt` is
  the version from differentiable scores.
* (c) `ProbabilityTheory.GEE.tendstoInMeasure_sandwichCovariance`: consistent bread and meat
  estimators give a consistent sandwich, for invertible `A`.
  `tendstoInMeasure_empirical_sandwichCovariance` applies it to the plug-in bread
  `n⁻¹ ∑ ∂U i/∂β (βhat n)` and meat `n⁻¹ ∑ U i (βhat n) U i (βhat n)ᵀ`, via the plug-in lemma
  `tendstoInMeasure_comp_of_tendstoUniformlyOn`. Its limit `sandwichCovariance (Abar β₀) (Bbar β₀)`
  is the covariance of the CLT only when the in-probability meat limit `Bbar β₀` equals the CLT
  meat `B`; `tendstoInMeasure_empirical_sandwichCovariance_of_eq` takes that identification as a
  hypothesis and concludes convergence to `sandwichCovariance (Abar β₀) B`.

The CLT hypotheses pin down the meat `B` only through its quadratic form `⟪B t, t⟫`, so `B`
is not required to be self-adjoint there: `sandwichCovariance A B` symmetrizes `B`
(`symmetrizedMeat`), which leaves the quadratic form unchanged
(`inner_symmetrizedMeat_apply`) and makes the sandwich self-adjoint
(`isSelfAdjoint_sandwichCovariance`), so it is a genuine covariance operator even for a
non-self-adjoint representative `B` (for example `B = I + J` with `J` skew-adjoint). For a
self-adjoint `B`, symmetrization is the identity
(`sandwichCovariance_eq_of_isSelfAdjoint`). The plug-in meat is a limit of self-adjoint
rank-one operators, so matching it with `B` as operators presupposes a self-adjoint `B`.

## Proof

The CLT goes through the cluster sums: by Cramér–Wold (`TendstoInDistribution.of_inner`) it
suffices to treat each projection `⟪(√n)⁻¹ • ∑ U k, t⟫ = ∑ (√n)⁻¹ ⟪U k, t⟫`, a row sum of a
triangular array of independent, mean-zero, square-integrable variables, to which the
repository's Lindeberg–Feller theorem `lindeberg_feller_clt_triangular` applies. For the
estimator, `tendstoInDistribution_sqrt_smul_sub_sandwich` applies this CLT to the transformed
cluster scores `-A⁻¹ U k β₀`, whose projection on `t` is the projection of `U k β₀` on
`-A⁻ᵀ t`, with variance `⟪A⁻¹ B A⁻ᵀ t, t⟫`. The difference between `√n (βhat n - β₀)` and
`-A⁻¹ (√n)⁻¹ ∑ U k β₀` is bounded by a small multiple of the latter on events of probability
tending to one, and the latter is tight (`isTightMeasureSet_of_tendsto_charFun`), so the
difference tends to `0` in probability and Slutsky's lemma
(`tendstoInDistribution_of_tendstoInMeasure_sub`) transfers the limit. No delta method is used.
Sandwich consistency is continuity of `(A, B) ↦ A⁻¹ B A⁻ᵀ` at an invertible `A`
(`NormedRing.inverse_continuousAt`).

`lindeberg_feller_clt_triangular` is stated for a positive limiting variance. A direction with
limiting variance `0` is handled separately: Chebyshev's inequality shows that the projected sum
tends to `0` in probability, which is convergence in distribution to `gaussianReal 0 0`.

## Source receipt

* K.-Y. Liang and S. L. Zeger, *Longitudinal data analysis using generalized linear models*,
  Biometrika 73 (1986), 13–22: the GEE estimator and its sandwich covariance (Theorem 2).
* A. W. van der Vaart, *Asymptotic Statistics* (1998): Theorem 5.9 (consistency of
  Z-estimators), Proposition 2.27 (multivariate Lindeberg–Feller theorem), §5.3 (asymptotic
  normality of Z-estimators).
* P. J. Huber, *The behavior of maximum likelihood estimates under nonstandard conditions*,
  Proc. Fifth Berkeley Symp. Math. Statist. Probab. 1 (1967), 221–233: the sandwich form
  `A⁻¹ B A⁻ᵀ`.

Reuse search (2026-11-11, pinned Mathlib and this repository): no GEE, sandwich, multivariate
Z-estimator or non-identically distributed multivariate CLT exists. The closest declarations are
the one-dimensional i.i.d. `tendstoInDistribution_sqrt_mul_sub_of_estimatingEquation`
(`MLEAsymptoticNormality`) and the i.i.d. `tendstoInDistribution_inv_sqrt_smul_sum_sub`
(`MultivariateCLT`); neither covers independent non-identical clusters. This file reuses
`lindeberg_feller_clt_triangular`, `TendstoInDistribution.of_inner`,
`tendstoInDistribution_of_tendstoInMeasure_sub`, `isTightMeasureSet_of_tendsto_charFun`,
`NormedRing.inverse_continuousAt` and `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`.
-/

@[expose] public section

open MeasureTheory Filter Finset RealInnerProductSpace
open scoped Real Topology ENNReal

namespace ProbabilityTheory.GEE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- A sequence of random vectors converging in distribution is bounded in probability: for every
`ε > 0` there is a radius `K` with `P {K < ‖X n‖} ≤ ε` for all `n`. -/
theorem exists_forall_measure_lt_norm_le_of_tendstoInDistribution {X : ℕ → Ω → E} {Z : Ω' → E}
    (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P') {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ n, P {ω | K < ‖X n ω‖} ≤ ε := by
  have hT : IsTightMeasureSet (Set.range fun n ↦ P.map (X n)) :=
    isTightMeasureSet_of_tendsto_charFun (f := charFun (P'.map Z))
      continuous_charFun.continuousAt fun t ↦ h.tendsto_charFun t
  obtain ⟨K, hK⟩ :=
    ((tendsto_measure_norm_gt_of_isTightMeasureSet hT).eventually (eventually_le_nhds hε)).exists
  refine ⟨K, fun n ↦ ?_⟩
  have hmeas : MeasurableSet {x : E | K < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  calc P {ω | K < ‖X n ω‖} = P.map (X n) {x | K < ‖x‖} :=
        (Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hmeas).symm
    _ ≤ ⨆ μ ∈ Set.range fun n ↦ P.map (X n), μ {x | K < ‖x‖} :=
        le_biSup (f := fun μ : Measure E ↦ μ {x | K < ‖x‖}) ⟨n, rfl⟩
    _ ≤ ε := hK

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private lemma inner_inv_sqrt_smul_sum (U : ℕ → Ω → E) (t : E) (n : ℕ) (ω : Ω) :
    ⟪(√n)⁻¹ • ∑ k ∈ range n, U k ω, t⟫ = ∑ k ∈ range n, (√n)⁻¹ * ⟪U k ω, t⟫ := by
  rw [real_inner_smul_left, sum_inner, Finset.mul_sum]

/-- **Central limit theorem for independent clusters** (Lindeberg form). Let `U k : Ω → E` be
independent, mean-zero, square-integrable cluster scores in a finite-dimensional real inner
product space. Suppose that for every direction `t`

* the averaged projected variances `n⁻¹ ∑_{k<n} E[⟪U k, t⟫²]` converge to `q t` (necessarily
  `q t ≥ 0`; `q t = 0` is allowed), and
* the projected triangular array `(√n)⁻¹ ⟪U k, t⟫`, `k < n`, satisfies the repository's
  Lindeberg condition `LindebergConditionTriangular`.

Then `(√n)⁻¹ • ∑_{k<n} U k` converges in distribution to any `Y` whose projections `⟪Y, t⟫` are
centered Gaussians of variance `q t`. The proof is Cramér–Wold plus the Lindeberg–Feller theorem
`lindeberg_feller_clt_triangular` applied to the cluster sums of each projection with `q t > 0`,
and Chebyshev's inequality for the projections with `q t = 0`. -/
theorem tendstoInDistribution_inv_sqrt_smul_sum_of_lindeberg {U : ℕ → Ω → E} {Y : Ω' → E}
    {q : E → ℝ} (hY : AEMeasurable Y P')
    (hYlaw : ∀ t, HasLaw (fun ω ↦ ⟪Y ω, t⟫) (gaussianReal 0 (q t).toNNReal) P')
    (hmeas : ∀ k, Measurable (U k)) (hindep : iIndepFun U P)
    (hmean : ∀ k, ∫ ω, U k ω ∂P = 0) (hL2 : ∀ k, MemLp (U k) 2 P)
    (hvar : ∀ t, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ ω, ⟪U k ω, t⟫ ^ 2 ∂P)
      atTop (𝓝 (q t)))
    (hL : ∀ t, LindebergConditionTriangular (fun n k ω ↦ (√n)⁻¹ * ⟪U k ω, t⟫) P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ • ∑ k ∈ range n, U k ω) atTop Y
      (fun _ ↦ P) P' := by
  have hSmeas : ∀ n : ℕ, AEMeasurable (fun ω ↦ (√n)⁻¹ • ∑ k ∈ range n, U k ω) P := fun n ↦
    ((Finset.measurable_sum _ fun k _ ↦ hmeas k).const_smul _).aemeasurable
  refine TendstoInDistribution.of_inner hY hSmeas fun t ↦ ?_
  have hinner_meas : Measurable fun x : E ↦ ⟪x, t⟫ :=
    (continuous_id.inner continuous_const).measurable
  set X : ℕ → ℕ → Ω → ℝ := fun n k ω ↦ (√n)⁻¹ * ⟪U k ω, t⟫ with hX_def
  have hXmeas : ∀ n k, Measurable (X n k) := fun n k ↦
    (hinner_meas.comp (hmeas k)).const_mul _
  have hind : ∀ n, iIndepFun ((Finset.range n).restrict (X n)) P := fun n ↦
    (hindep.comp (fun _ x ↦ (√n)⁻¹ * ⟪x, t⟫) fun _ ↦ hinner_meas.const_mul _).precomp
      (g := ((↑) : Finset.range n → ℕ)) Subtype.val_injective
  have hXmean : ∀ n, ∀ k ∈ Finset.range n, ∫ ω, X n k ω ∂P = 0 := by
    intro n k _
    simp only [hX_def, integral_const_mul]
    have h : ∫ ω, ⟪U k ω, t⟫ ∂P = 0 := by
      have h' := integral_inner (𝕜 := ℝ) ((hL2 k).integrable one_le_two) t
      rw [hmean k, inner_zero_right] at h'
      rw [← h']
      exact integral_congr_ae (ae_of_all _ fun ω ↦ real_inner_comm _ _)
    rw [h, mul_zero]
  have hXL2 : ∀ n k, MemLp (X n k) 2 P := fun n k ↦ ((hL2 k).inner_const t).const_mul _
  have hXint2 : ∀ n, ∀ k ∈ Finset.range n, Integrable (fun ω ↦ (X n k ω) ^ 2) P :=
    fun n k _ ↦ (hXL2 n k).integrable_sq
  have hXvar' : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ∫ ω, (X n k ω) ^ 2 ∂P) atTop
      (𝓝 (q t)) := by
    refine (hvar t).congr fun n ↦ ?_
    simp only [hX_def, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), integral_const_mul,
      Finset.mul_sum]
  have hq0 : 0 ≤ q t := ge_of_tendsto' (hvar t) fun n ↦ mul_nonneg (inv_nonneg.2 n.cast_nonneg)
    (Finset.sum_nonneg fun k _ ↦ integral_nonneg fun ω ↦ sq_nonneg _)
  have hS : ∀ n : ℕ, (fun ω ↦ ⟪(√n)⁻¹ • ∑ k ∈ range n, U k ω, t⟫) =
      ∑ k ∈ Finset.range n, X n k := fun n ↦ by
    ext ω
    rw [Finset.sum_apply, inner_inv_sqrt_smul_sum]
  rcases hq0.lt_or_eq with hq | hq
  swap
  · -- degenerate direction, `q t = 0`: Chebyshev gives convergence in probability to `0`
    have hSmean : ∀ n, P[∑ k ∈ Finset.range n, X n k] = 0 := fun n ↦ by
      simp only [Finset.sum_apply]
      rw [integral_finsetSum _ fun k _ ↦ (hXL2 n k).integrable one_le_two]
      exact Finset.sum_eq_zero fun k hk ↦ hXmean n k hk
    have hSvar : ∀ n, Var[∑ k ∈ Finset.range n, X n k; P] =
        ∑ k ∈ Finset.range n, ∫ ω, (X n k ω) ^ 2 ∂P := fun n ↦ by
      rw [IndepFun.variance_sum (fun k _ ↦ hXL2 n k) fun i _ j _ hij ↦
        (hindep.indepFun hij).comp (hinner_meas.const_mul _) (hinner_meas.const_mul _)]
      exact Finset.sum_congr rfl fun k hk ↦
        variance_of_integral_eq_zero (hXmeas n k).aemeasurable (hXmean n k hk)
    have hconv : TendstoInMeasure P (fun n ↦ ∑ k ∈ Finset.range n, X n k) atTop
        (fun _ ↦ 0) := by
      rw [tendstoInMeasure_iff_dist]
      intro ε hε
      have hlim : Tendsto (fun n ↦ ENNReal.ofReal
          (Var[∑ k ∈ Finset.range n, X n k; P] / ε ^ 2)) atTop (𝓝 0) := by
        have h := (ENNReal.continuous_ofReal.tendsto _).comp (hXvar'.div_const (ε ^ 2))
        rw [← hq, zero_div, ENNReal.ofReal_zero] at h
        simp only [hSvar]
        exact h
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun _ ↦ zero_le) fun n ↦ ?_
      have h := meas_ge_le_variance_div_sq
        (memLp_finsetSum' (Finset.range n) fun k _ ↦ hXL2 n k) hε
      simpa only [hSmean, sub_zero, Real.dist_eq] using h
    have hD := hconv.tendstoInDistribution_of_aemeasurable
      (fun n ↦ Finset.aemeasurable_sum _ fun k _ ↦ (hXmeas n k).aemeasurable) aemeasurable_const
    refine ⟨fun n ↦ hinner_meas.comp_aemeasurable (hSmeas n), (hYlaw t).aemeasurable, ?_⟩
    have hlaw : (P'.map fun ω ↦ ⟪Y ω, t⟫) = P.map fun _ ↦ (0 : ℝ) := by
      rw [(hYlaw t).map_eq, Measure.map_const, measure_univ, one_smul, ← hq,
        Real.toNNReal_zero, gaussianReal_zero_var]
    simp only [hS, hlaw]
    exact hD.tendsto
  set σ := √(q t) with hσ_def
  have hσ : 0 < σ := Real.sqrt_pos.2 hq
  have hσ2 : σ ^ 2 = q t := Real.sq_sqrt hq.le
  have hXvar : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ∫ ω, (X n k ω) ^ 2 ∂P) atTop
      (𝓝 (σ ^ 2)) := hσ2 ▸ hXvar'
  have hLF := lindeberg_feller_clt_triangular X hind (fun n k _ ↦ hXmeas n k) hXmean hXint2 σ hσ
    hXvar (hL t)
  refine ⟨fun n ↦ hinner_meas.comp_aemeasurable (hSmeas n), (hYlaw t).aemeasurable, ?_⟩
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f ↦ ?_
  have hlaw : (P'.map fun ω ↦ ⟪Y ω, t⟫) = gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ := by
    rw [(hYlaw t).map_eq]
    congr 1
    apply NNReal.eq
    rw [Real.coe_toNNReal _ hq.le]
    exact hσ2.symm
  simp only [ProbabilityMeasure.coe_mk, hlaw]
  convert hLF f using 3 with n
  congr 1
  ext ω
  exact inner_inv_sqrt_smul_sum U t n ω

/-! ### Consistency of an estimating-equation root -/

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [IsProbabilityMeasure P] in
/-- **Consistency of a root of a cluster estimating equation** (Z-estimator consistency).

Let `U i β ω` be the score of cluster `i` at parameter `β`. Suppose that, on a compact parameter
set `K`,

* (uniform convergence) the averaged estimating function `n⁻¹ • ∑_{i<n} U i β` converges to a
  deterministic `g β` uniformly on `K` in probability,
* (identifiability) `g` is continuous on `K` and `β₀` is its only zero in `K`,
* (root in the neighbourhood) the estimator `βhat n` lies in `K` and solves the estimating
  equation `∑_{i<n} U i (βhat n) = 0`, each with probability tending to one.

Then `βhat n → β₀` in probability. The probabilities of the possibly non-measurable events
are outer measures, so no measurability of `βhat` or of the supremum is needed. -/
theorem tendstoInMeasure_of_tendstoUniformlyOn_of_root {U : ℕ → E → Ω → E} {g : E → E}
    {K : Set E} (hK : IsCompact K) (hg : ContinuousOn g K) {β₀ : E}
    (hident : ∀ β ∈ K, g β = 0 → β = β₀)
    (hunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦
      P {ω | ∃ β ∈ K, ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, U i β ω - g β‖}) atTop (𝓝 0))
    {βhat : ℕ → Ω → E} (hβK : Tendsto (fun n ↦ P {ω | βhat n ω ∉ K}) atTop (𝓝 0))
    (hroot : Tendsto (fun n ↦ P {ω | ∑ i ∈ range n, U i (βhat n ω) ω ≠ 0}) atTop (𝓝 0)) :
    TendstoInMeasure P βhat atTop (fun _ ↦ β₀) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  -- well-separatedness of the zero `β₀`
  obtain ⟨η, hη, hsep⟩ : ∃ η > 0, ∀ β ∈ K, ε ≤ ‖β - β₀‖ → η ≤ ‖g β‖ := by
    set C := K ∩ {β | ε ≤ ‖β - β₀‖}
    rcases C.eq_empty_or_nonempty with hC | hC
    · refine ⟨1, one_pos, fun β hβ hβε ↦ ?_⟩
      exact absurd (show β ∈ C from ⟨hβ, hβε⟩) (hC ▸ Set.notMem_empty β)
    have hCc : IsCompact C :=
      hK.inter_right (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
    obtain ⟨β₁, hβ₁, hmin⟩ := hCc.exists_isMinOn hC (hg.mono Set.inter_subset_left).norm
    refine ⟨‖g β₁‖, norm_pos_iff.2 fun h0 ↦ ?_, fun β hβ hβε ↦ hmin ⟨hβ, hβε⟩⟩
    have h1 : ε ≤ ‖β₁ - β₀‖ := hβ₁.2
    rw [hident β₁ hβ₁.1 h0, sub_self, norm_zero] at h1
    exact hε.not_ge h1
  have hsum := (hβK.add hroot).add (hunif η hη)
  rw [add_zero, add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
    fun n ↦ (measure_mono fun ω hω ↦ ?_).trans ((measure_union_le _ _).trans
      (add_le_add_left (measure_union_le _ _) _))
  simp only [Set.mem_ofPred_eq] at hω
  by_cases hK' : βhat n ω ∈ K
  · by_cases hr : ∑ i ∈ range n, U i (βhat n ω) ω = 0
    · refine Or.inr ⟨βhat n ω, hK', ?_⟩
      rw [hr, smul_zero, zero_sub, norm_neg]
      exact hsep _ hK' hω
    · exact Or.inl (Or.inr hr)
  · exact Or.inl (Or.inl hK')

/-! ### Linearization and asymptotic normality -/

/-- **Asymptotic normality from a linearization** of the cluster estimating equation.

Let `A` be invertible (the sensitivity matrix), let `βhat n` solve `∑_{i<n} U i (βhat n) = 0`
with probability tending to one, and suppose the averaged estimating function is
differentiable at `β₀` along the estimator in probability, with derivative `A`:
for every `ε > 0`, with probability tending to one,
`‖n⁻¹ • (∑ U i (βhat n) - ∑ U i β₀) - A (βhat n - β₀)‖ ≤ ε ‖βhat n - β₀‖`.
If the cluster sums `-A⁻¹ ((√n)⁻¹ • ∑_{i<n} U i β₀)` converge in distribution to `W`, then so
does `√n • (βhat n - β₀)`.

The limit is fed through the cluster sums themselves: this theorem only transfers the cluster
CLT for `U i β₀` to the estimator. -/
theorem tendstoInDistribution_sqrt_smul_sub_of_linearization {U : ℕ → E → Ω → E} {β₀ : E}
    {A : E →L[ℝ] E} (hA : IsUnit A) {W : Ω' → E}
    (hX : TendstoInDistribution
      (fun (n : ℕ) ω ↦ -Ring.inverse A ((√n)⁻¹ • ∑ i ∈ range n, U i β₀ ω)) atTop W
      (fun _ ↦ P) P')
    {βhat : ℕ → Ω → E} (hβ : ∀ n, AEMeasurable (βhat n) P)
    (hroot : Tendsto (fun n ↦ P {ω | ∑ i ∈ range n, U i (βhat n ω) ω ≠ 0}) atTop (𝓝 0))
    (hlin : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ε * ‖βhat n ω - β₀‖ <
      ‖(n : ℝ)⁻¹ • (∑ i ∈ range n, U i (βhat n ω) ω - ∑ i ∈ range n, U i β₀ ω) -
        A (βhat n ω - β₀)‖}) atTop (𝓝 0)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n • (βhat n ω - β₀)) atTop W (fun _ ↦ P) P' := by
  set Ai := Ring.inverse A with hAi_def
  have hAiA : Ai * A = 1 := Ring.inverse_mul_cancel A hA
  set X : ℕ → Ω → E := fun n ω ↦ -Ai ((√n)⁻¹ • ∑ i ∈ range n, U i β₀ ω) with hX_def
  set T : ℕ → Ω → E := fun n ω ↦ √n • (βhat n ω - β₀) with hT_def
  refine tendstoInDistribution_of_tendstoInMeasure_sub (X := X) T W hX ?_
    fun n ↦ (hβ n).sub_const _ |>.const_smul _
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨K₀, hK₀⟩ := exists_forall_measure_lt_norm_le_of_tendstoInDistribution hX
    (ENNReal.half_pos hδ.ne')
  set K := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  set a := ‖Ai‖
  have ha : 0 ≤ a := norm_nonneg _
  set c := min (1 / (2 * (a + 1))) (ε / (4 * (a + 1) * (K + 1)))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hac : a * c ≤ 1 / 2 := by
    calc a * c ≤ (a + 1) * (1 / (2 * (a + 1))) :=
          mul_le_mul (by linarith) (min_le_left _ _) hc.le (by positivity)
      _ = 1 / 2 := by field_simp
  have hacK : 2 * (a * c) * K < ε := by
    have h1 : c * (4 * (a + 1) * (K + 1)) ≤ ε :=
      (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    nlinarith [mul_nonneg ha hK, mul_nonneg hc.le hK, mul_nonneg (mul_nonneg ha hc.le) hK]
  have hev : ∀ᶠ n in atTop, P {ω | ∑ i ∈ range n, U i (βhat n ω) ω ≠ 0} +
      P {ω | c * ‖βhat n ω - β₀‖ < ‖(n : ℝ)⁻¹ • (∑ i ∈ range n, U i (βhat n ω) ω -
        ∑ i ∈ range n, U i β₀ ω) - A (βhat n ω - β₀)‖} ≤ δ / 2 := by
    have h0 := (hroot.add (hlin c hc))
    rw [add_zero] at h0
    exact h0.eventually (eventually_le_nhds (ENNReal.half_pos hδ.ne'))
  filter_upwards [hev] with n hn
  refine (measure_mono (t := {ω | ∑ i ∈ range n, U i (βhat n ω) ω ≠ 0} ∪
    {ω | c * ‖βhat n ω - β₀‖ < ‖(n : ℝ)⁻¹ • (∑ i ∈ range n, U i (βhat n ω) ω -
        ∑ i ∈ range n, U i β₀ ω) - A (βhat n ω - β₀)‖} ∪ {ω | K₀ < ‖X n ω‖})
    fun ω hω ↦ ?_).trans ?_
  · simp only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.zero_apply, sub_zero] at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨hr, hl⟩, hXK⟩ := hcon
    set d := βhat n ω - β₀
    set r : E := (n : ℝ)⁻¹ • (∑ i ∈ range n, U i (βhat n ω) ω - ∑ i ∈ range n, U i β₀ ω) - A d
    have hXK' : ‖X n ω‖ ≤ K := hXK.trans (le_max_left _ _)
    -- `T - X = -Ai (√n • r)`
    have hsq : √(n : ℝ) * (n : ℝ)⁻¹ = (√(n : ℝ))⁻¹ := by
      rw [← div_eq_mul_inv, Real.sqrt_div_self', one_div]
    have hTX : T n ω - X n ω = -Ai (√n • r) := by
      have hAiAd : Ai (A (√n • d)) = √n • d := by
        rw [← mul_apply_eq_comp, hAiA, one_apply_eq_self]
      simp only [hT_def, hX_def, r, hr, zero_sub, smul_sub, smul_neg, smul_smul, hsq, map_sub,
        map_neg, ← map_smul A, hAiAd]
      simp only [d, smul_sub]
      abel
    have hTXn : ‖T n ω - X n ω‖ ≤ a * c * ‖T n ω‖ := by
      rw [hTX, norm_neg]
      calc ‖Ai (√n • r)‖ ≤ a * ‖√n • r‖ := Ai.le_opNorm _
        _ = a * (√n * ‖r‖) := by rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ a * (√n * (c * ‖d‖)) := by gcongr
        _ = a * c * ‖T n ω‖ := by
          rw [hT_def]
          simp only [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
          ring
    have hT : ‖T n ω‖ ≤ ‖X n ω‖ + ‖T n ω - X n ω‖ := norm_le_insert' _ _
    have hTn : ‖T n ω‖ ≤ 2 * K := by
      nlinarith [norm_nonneg (T n ω), mul_le_mul_of_nonneg_right hac (norm_nonneg (T n ω))]
    have : ‖T n ω - X n ω‖ < ε := by
      calc ‖T n ω - X n ω‖ ≤ a * c * ‖T n ω‖ := hTXn
        _ ≤ a * c * (2 * K) := by gcongr
        _ = 2 * (a * c) * K := by ring
        _ < ε := hacK
    exact this.not_ge hω
  · calc _ ≤ P ({ω | ∑ i ∈ range n, U i (βhat n ω) ω ≠ 0} ∪
          {ω | c * ‖βhat n ω - β₀‖ < ‖(n : ℝ)⁻¹ • (∑ i ∈ range n, U i (βhat n ω) ω -
            ∑ i ∈ range n, U i β₀ ω) - A (βhat n ω - β₀)‖}) + P {ω | K₀ < ‖X n ω‖} :=
          measure_union_le _ _
      _ ≤ δ / 2 + δ / 2 := by
          gcongr
          · exact (measure_union_le _ _).trans hn
          · exact hK₀ n
      _ = δ := ENNReal.add_halves δ

/-! ### The sandwich covariance and the GEE central limit theorem -/

/-- The **symmetrized meat** `(B + B†) / 2`. It has the same quadratic form as `B`, and
it is self-adjoint, unlike an arbitrary quadratic-form representative of `B`. -/
noncomputable def symmetrizedMeat (B : E →L[ℝ] E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) • (B + ContinuousLinearMap.adjoint B)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The quadratic form of the symmetrized meat is the quadratic form of `B`. -/
theorem inner_symmetrizedMeat_apply (B : E →L[ℝ] E) (t : E) :
    ⟪symmetrizedMeat B t, t⟫ = ⟪B t, t⟫ := by
  have h : ⟪ContinuousLinearMap.adjoint B t, t⟫ = ⟪B t, t⟫ := by
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  simp only [symmetrizedMeat, add_apply, smul_apply, real_inner_smul_left, inner_add_left, h]
  ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- The symmetrized meat is self-adjoint. -/
theorem isSelfAdjoint_symmetrizedMeat (B : E →L[ℝ] E) : IsSelfAdjoint (symmetrizedMeat B) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  show ContinuousLinearMap.adjoint (symmetrizedMeat B) = symmetrizedMeat B
  simp only [symmetrizedMeat, map_smulₛₗ, map_add, ContinuousLinearMap.adjoint_adjoint,
    starRingEnd_apply, star_trivial]
  rw [add_comm (ContinuousLinearMap.adjoint B) B]

/-- The **sandwich covariance** `A⁻¹ ((B + B†) / 2) A⁻ᵀ` built from a bread (sensitivity)
matrix `A` and a meat (variability) matrix `B`, where `A⁻ᵀ` is the adjoint of
`A⁻¹ = Ring.inverse A`. The meat is symmetrized before sandwiching: only its quadratic
form is identified by the CLT hypotheses, and symmetrization makes the sandwich
self-adjoint (`isSelfAdjoint_sandwichCovariance`) without changing its quadratic form
(`inner_sandwichCovariance_apply`). For a singular `A` the junk value
`Ring.inverse A = 0` gives `0`. -/
noncomputable def sandwichCovariance (A B : E →L[ℝ] E) : E →L[ℝ] E :=
  Ring.inverse A * symmetrizedMeat B *
    ContinuousLinearMap.adjoint (Ring.inverse A)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The sandwich covariance is self-adjoint for every meat `B`. -/
theorem isSelfAdjoint_sandwichCovariance (A B : E →L[ℝ] E) :
    IsSelfAdjoint (sandwichCovariance A B) := by
  have hc := (isSelfAdjoint_symmetrizedMeat B).conj_adjoint (Ring.inverse A)
  rwa [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def] at hc

omit [MeasurableSpace E] [BorelSpace E] in
/-- For a self-adjoint meat, symmetrization is the identity, so the sandwich is the
unsymmetrized `A⁻¹ B A⁻ᵀ`. -/
theorem sandwichCovariance_eq_of_isSelfAdjoint {A B : E →L[ℝ] E} (hB : IsSelfAdjoint B) :
    sandwichCovariance A B =
      Ring.inverse A * B * ContinuousLinearMap.adjoint (Ring.inverse A) := by
  have hsym : symmetrizedMeat B = B := by
    rw [symmetrizedMeat, hB.adjoint_eq, ← two_smul ℝ B, smul_smul]
    norm_num
  rw [sandwichCovariance, hsym]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Symmetrization is idempotent. -/
theorem symmetrizedMeat_idempotent (B : E →L[ℝ] E) :
    symmetrizedMeat (symmetrizedMeat B) = symmetrizedMeat B := by
  rw [symmetrizedMeat, (isSelfAdjoint_symmetrizedMeat B).adjoint_eq, ← two_smul ℝ
    (symmetrizedMeat B), smul_smul]
  norm_num

omit [MeasurableSpace E] [BorelSpace E] in
/-- The sandwich depends on the meat only through its symmetrization. -/
theorem sandwichCovariance_symmetrizedMeat (A B : E →L[ℝ] E) :
    sandwichCovariance A (symmetrizedMeat B) = sandwichCovariance A B := by
  simp only [sandwichCovariance, symmetrizedMeat_idempotent]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The quadratic form of the sandwich is the meat evaluated at `A⁻ᵀ t`. -/
theorem inner_sandwichCovariance_apply (A B : E →L[ℝ] E) (t : E) :
    ⟪sandwichCovariance A B t, t⟫ =
      ⟪B (ContinuousLinearMap.adjoint (Ring.inverse A) t),
        ContinuousLinearMap.adjoint (Ring.inverse A) t⟫ := by
  simp only [sandwichCovariance, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_right, inner_symmetrizedMeat_apply]

/-- **Asymptotic normality of a GEE estimator with sandwich covariance.**

Let `U k β ω` be independent cluster scores. At the true parameter `β₀` assume the cluster
scores are measurable, independent, unbiased (`E[U k β₀] = 0`), and square integrable, that the
averaged projected variances converge to the meat quadratic form `⟪B t, t⟫` (the hypotheses
identify `B` only through this quadratic form; `B` need not be self-adjoint, and
`B` is not assumed positive definite), and that every projection satisfies the cluster
Lindeberg condition. Let the sensitivity matrix `A` be invertible, and let `βhat n` be a root
of the estimating equation with probability tending to one that linearizes with derivative
`A` (as in `tendstoInDistribution_sqrt_smul_sub_of_linearization`). Then
`√n • (βhat n - β₀)` converges in distribution to every `W` whose projections `⟪W, t⟫` are
centered Gaussians with variance `⟪A⁻¹ B A⁻ᵀ t, t⟫`, i.e. `W ∼ N(0, sandwichCovariance A B)`,
where the sandwich is the self-adjoint symmetrized covariance above.

The CLT is applied to the cluster sums of the transformed scores `-A⁻¹ U k β₀`. -/
theorem tendstoInDistribution_sqrt_smul_sub_sandwich {U : ℕ → E → Ω → E} {β₀ : E}
    {A B : E →L[ℝ] E} (hA : IsUnit A)
    (hmeas : ∀ k, Measurable (U k β₀)) (hindep : iIndepFun (fun k ↦ U k β₀) P)
    (hmean : ∀ k, ∫ ω, U k β₀ ω ∂P = 0) (hL2 : ∀ k, MemLp (U k β₀) 2 P)
    (hvar : ∀ t, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ ω, ⟪U k β₀ ω, t⟫ ^ 2 ∂P)
      atTop (𝓝 ⟪B t, t⟫))
    (hL : ∀ t, LindebergConditionTriangular (fun n k ω ↦ (√n)⁻¹ * ⟪U k β₀ ω, t⟫) P)
    {βhat : ℕ → Ω → E} (hβ : ∀ n, AEMeasurable (βhat n) P)
    (hroot : Tendsto (fun n ↦ P {ω | ∑ i ∈ range n, U i (βhat n ω) ω ≠ 0}) atTop (𝓝 0))
    (hlin : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ε * ‖βhat n ω - β₀‖ <
      ‖(n : ℝ)⁻¹ • (∑ i ∈ range n, U i (βhat n ω) ω - ∑ i ∈ range n, U i β₀ ω) -
        A (βhat n ω - β₀)‖}) atTop (𝓝 0))
    {W : Ω' → E} (hW : AEMeasurable W P')
    (hWlaw : ∀ t, HasLaw (fun ω ↦ ⟪W ω, t⟫)
      (gaussianReal 0 (⟪sandwichCovariance A B t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n • (βhat n ω - β₀)) atTop W (fun _ ↦ P) P' := by
  set Ai := Ring.inverse A with hAi_def
  set s : E → E := fun t ↦ -ContinuousLinearMap.adjoint Ai t with hs_def
  set V : ℕ → Ω → E := fun k ω ↦ -Ai (U k β₀ ω) with hV_def
  have hVinner : ∀ k ω t, ⟪V k ω, t⟫ = ⟪U k β₀ ω, s t⟫ := by
    intro k ω t
    simp only [hV_def, hs_def, inner_neg_left, inner_neg_right,
      ContinuousLinearMap.adjoint_inner_right]
  have hq : ∀ t, ⟪B (s t), s t⟫ = ⟪sandwichCovariance A B t, t⟫ := by
    intro t
    simp only [hs_def, map_neg, inner_neg_neg, inner_sandwichCovariance_apply, hAi_def]
  have hCLT : TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ • ∑ k ∈ range n, V k ω) atTop W
      (fun _ ↦ P) P' := by
    refine tendstoInDistribution_inv_sqrt_smul_sum_of_lindeberg hW hWlaw
      (fun k ↦ (Ai.continuous.measurable.comp (hmeas k)).neg)
      (hindep.comp (fun _ x ↦ -Ai x) fun _ ↦ Ai.continuous.measurable.neg)
      (fun k ↦ ?_) (fun k ↦ ((hL2 k).continuousLinearMap_comp Ai).neg) (fun t ↦ ?_)
      (fun t ↦ ?_)
    · simp only [hV_def, integral_neg, Ai.integral_comp_comm ((hL2 k).integrable one_le_two),
        hmean k, map_zero, neg_zero]
    · simp_rw [hVinner, ← hq]
      exact hvar (s t)
    · simp_rw [hVinner]
      exact hL (s t)
  refine tendstoInDistribution_sqrt_smul_sub_of_linearization hA ?_ hβ hroot hlin
  refine hCLT.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
  simp only [hV_def, map_smul, map_sum, smul_neg, Finset.sum_neg_distrib, ← hAi_def]

/-! ### Plug-in consistency, bread, meat and sandwich -/

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [IsProbabilityMeasure P] in
/-- **Plug-in consistency.** If random functions `Φ n β` converge to `φ β` uniformly on a
ball around `β₀` in probability, `φ` is continuous at `β₀`, and `βhat n → β₀` in probability,
then `Φ n (βhat n) → φ β₀` in probability. -/
theorem tendstoInMeasure_comp_of_tendstoUniformlyOn {F : Type*} [PseudoMetricSpace F]
    {Φ : ℕ → E → Ω → F} {φ : E → F} {β₀ : E} {δ : ℝ} (hδ : 0 < δ) (hφ : ContinuousAt φ β₀)
    (hunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦
      P {ω | ∃ β ∈ Metric.ball β₀ δ, ε ≤ dist (Φ n β ω) (φ β)}) atTop (𝓝 0))
    {βhat : ℕ → Ω → E} (hcons : TendstoInMeasure P βhat atTop (fun _ ↦ β₀)) :
    TendstoInMeasure P (fun n ω ↦ Φ n (βhat n ω) ω) atTop (fun _ ↦ φ β₀) := by
  rw [tendstoInMeasure_iff_dist] at hcons ⊢
  intro ε hε
  obtain ⟨r₀, hr₀, hφr⟩ := Metric.continuousAt_iff.1 hφ (ε / 2) (half_pos hε)
  set r := min r₀ δ
  have hr : 0 < r := lt_min hr₀ hδ
  have hsum := (hcons r hr).add (hunif (ε / 2) (half_pos hε))
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
    fun n ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hball : βhat n ω ∈ Metric.ball β₀ δ :=
    Metric.mem_ball.2 (h1.trans_le (min_le_right _ _))
  have h3 : dist (Φ n (βhat n ω) ω) (φ (βhat n ω)) < ε / 2 := h2 _ hball
  have h4 : dist (φ (βhat n ω)) (φ β₀) < ε / 2 := hφr (h1.trans_le (min_le_left _ _))
  linarith [dist_triangle (Φ n (βhat n ω) ω) (φ (βhat n ω)) (φ β₀)]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [IsProbabilityMeasure P] in
/-- **Linearization from differentiability (proved input).** If each cluster score is
differentiable in `β` on a ball around `β₀` with derivative `DU i β ω`, the averaged Jacobian
`n⁻¹ • ∑ DU i β` converges uniformly on the ball in probability to a sensitivity function
`Abar β` continuous at `β₀`, and `βhat n → β₀` in probability, then the averaged estimating
function linearizes along `βhat` with derivative `Abar β₀`: this is the hypothesis `hlin` of
`tendstoInDistribution_sqrt_smul_sub_of_linearization`. -/
theorem linearization_of_hasFDerivAt {U : ℕ → E → Ω → E} {DU : ℕ → E → Ω → E →L[ℝ] E}
    {β₀ : E} {δ : ℝ} (hδ : 0 < δ)
    (hdiff : ∀ i ω, ∀ β ∈ Metric.ball β₀ δ, HasFDerivAt (fun b ↦ U i b ω) (DU i β ω) β)
    {Abar : E → E →L[ℝ] E} (hAbar : ContinuousAt Abar β₀)
    (hunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ β ∈ Metric.ball β₀ δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DU i β ω - Abar β‖}) atTop (𝓝 0))
    {βhat : ℕ → Ω → E} (hcons : TendstoInMeasure P βhat atTop (fun _ ↦ β₀)) :
    ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ε * ‖βhat n ω - β₀‖ <
      ‖(n : ℝ)⁻¹ • (∑ i ∈ range n, U i (βhat n ω) ω - ∑ i ∈ range n, U i β₀ ω) -
        Abar β₀ (βhat n ω - β₀)‖}) atTop (𝓝 0) := by
  intro ε hε
  rw [tendstoInMeasure_iff_norm] at hcons
  obtain ⟨r₀, hr₀, hAr⟩ := Metric.continuousAt_iff.1 hAbar (ε / 2) (half_pos hε)
  set r := min r₀ δ
  have hr : 0 < r := lt_min hr₀ hδ
  have hsum := (hcons r hr).add (hunif (ε / 2) (half_pos hε))
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
    fun n ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hsub : Metric.ball β₀ r ⊆ Metric.ball β₀ δ := Metric.ball_subset_ball (min_le_right _ _)
  set f : E → E := fun b ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, U i b ω - Abar β₀ b
  set f' : E → E →L[ℝ] E := fun b ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, DU i b ω - Abar β₀
  have hf : ∀ b ∈ Metric.ball β₀ r, HasFDerivWithinAt f (f' b) (Metric.ball β₀ r) b := by
    intro b hb
    exact (((HasFDerivAt.fun_sum fun i _ ↦ hdiff i ω b (hsub hb)).fun_const_smul
      ((n : ℝ)⁻¹)).fun_sub (Abar β₀).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ b ∈ Metric.ball β₀ r, ‖f' b‖ ≤ ε := by
    intro b hb
    have hb' : dist b β₀ < r₀ := (Metric.mem_ball.1 hb).trans_le (min_le_left _ _)
    calc ‖f' b‖ = ‖((n : ℝ)⁻¹ • ∑ i ∈ range n, DU i b ω - Abar b) + (Abar b - Abar β₀)‖ := by
          simp only [f', sub_add_sub_cancel]
      _ ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DU i b ω - Abar b‖ + ‖Abar b - Abar β₀‖ := norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := by
          gcongr
          · exact (h2 b (hsub hb)).le
          · have h3 := hAr hb'
            rw [dist_eq_norm] at h3
            exact h3.le
      _ = ε := add_halves ε
  have hβr : βhat n ω ∈ Metric.ball β₀ r := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact h1
  have hmv := (convex_ball β₀ r).norm_image_sub_le_of_norm_hasFDerivWithin_le hf hbound
    (Metric.mem_ball_self hr) hβr
  have heq : f (βhat n ω) - f β₀ = (n : ℝ)⁻¹ • (∑ i ∈ range n, U i (βhat n ω) ω -
      ∑ i ∈ range n, U i β₀ ω) - Abar β₀ (βhat n ω - β₀) := by
    simp only [f, smul_sub, map_sub]
    abel
  rw [heq] at hmv
  exact hω.not_ge hmv

omit [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure P] in
/-- **Consistency of the sandwich estimator.** If the bread estimators `Ahat n` converge in
probability to an invertible `A` and the meat estimators `Bhat n` converge in probability to
`B`, then the sandwich `Ahat⁻¹ Bhat Ahat⁻ᵀ` converges in probability to `A⁻¹ B A⁻ᵀ`, the
asymptotic covariance of `tendstoInDistribution_sqrt_smul_sub_sandwich`. -/
theorem tendstoInMeasure_sandwichCovariance {Ahat Bhat : ℕ → Ω → E →L[ℝ] E}
    {A B : E →L[ℝ] E} (hA : IsUnit A)
    (hAhat : TendstoInMeasure P Ahat atTop (fun _ ↦ A))
    (hBhat : TendstoInMeasure P Bhat atTop (fun _ ↦ B)) :
    TendstoInMeasure P (fun n ω ↦ sandwichCovariance (Ahat n ω) (Bhat n ω)) atTop
      (fun _ ↦ sandwichCovariance A B) := by
  have hcont : ContinuousAt (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) ↦ sandwichCovariance p.1 p.2)
      (A, B) := by
    have h1 : ContinuousAt Ring.inverse A := NormedRing.inverse_continuousAt hA.unit
    have hinv : ContinuousAt (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) ↦ Ring.inverse p.1) (A, B) :=
      ContinuousAt.comp (f := Prod.fst) (x := (A, B)) h1 continuous_fst.continuousAt
    have hadj : Continuous fun T : E →L[ℝ] E ↦ ContinuousLinearMap.adjoint T :=
      ContinuousLinearMap.adjoint.continuous
    have hsym : ContinuousAt (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) ↦ symmetrizedMeat p.2)
        (A, B) := by
      simp only [symmetrizedMeat]
      apply ContinuousAt.const_smul _ (1 / 2 : ℝ)
      exact continuous_snd.continuousAt.add
        (hadj.continuousAt.comp continuous_snd.continuousAt)
    simp only [sandwichCovariance]
    exact (hinv.mul hsym).mul (hadj.continuousAt.comp hinv)
  -- a direct `ε`-`δ` argument; avoids convergence in measure on the product space
  rw [tendstoInMeasure_iff_dist] at hAhat hBhat ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hcont ε hε
  have hsum := (hAhat δ hδ).add (hBhat δ hδ)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
    fun n ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  have h := hδε (x := (Ahat n ω, Bhat n ω)) (by rw [Prod.dist_eq]; exact max_lt hcon.1 hcon.2)
  exact h.not_ge hω

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The quadratic form of the rank-one operator `u uᵀ`, Mathlib's
`InnerProductSpace.rankOne ℝ u u`, is `⟪u, t⟫²`. -/
theorem inner_rankOne_apply (u t : E) :
    ⟪InnerProductSpace.rankOne ℝ u u t, t⟫ = ⟪u, t⟫ ^ 2 := by
  simp only [InnerProductSpace.rankOne_apply, real_inner_smul_left, sq]

omit [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure P] in
/-- **Consistency of the empirical sandwich estimator** `Ahat⁻¹ Bhat Ahat⁻ᵀ` with plug-in bread
`Ahat n = n⁻¹ • ∑_{i<n} DU i (βhat n)` and plug-in meat
`Bhat n = n⁻¹ • ∑_{i<n} U i (βhat n) U i (βhat n)ᵀ`. Assume the averaged Jacobians and the
averaged rank-one operators of the cluster scores converge uniformly on a ball around `β₀` in
probability to `Abar` and `Bbar`, both continuous at `β₀`, that `Abar β₀` is invertible, and
that `βhat` is consistent. Then the empirical sandwich converges in probability to
`sandwichCovariance (Abar β₀) (Bbar β₀)`.

This is the asymptotic covariance of `tendstoInDistribution_sqrt_smul_sub_sandwich_of_hasFDerivAt`
(same `Abar` and Jacobian hypothesis) only when `Bbar β₀` equals the CLT meat `B`, which this
theorem does not assume; see `tendstoInMeasure_empirical_sandwichCovariance_of_eq`. -/
theorem tendstoInMeasure_empirical_sandwichCovariance {U : ℕ → E → Ω → E}
    {DU : ℕ → E → Ω → E →L[ℝ] E} {β₀ : E} {δ : ℝ} (hδ : 0 < δ)
    {Abar Bbar : E → E →L[ℝ] E} (hAbar : ContinuousAt Abar β₀) (hBbar : ContinuousAt Bbar β₀)
    (hA : IsUnit (Abar β₀))
    (hAunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ β ∈ Metric.ball β₀ δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DU i β ω - Abar β‖}) atTop (𝓝 0))
    (hBunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ β ∈ Metric.ball β₀ δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, InnerProductSpace.rankOne ℝ (U i β ω) (U i β ω) -
        Bbar β‖}) atTop (𝓝 0))
    {βhat : ℕ → Ω → E} (hcons : TendstoInMeasure P βhat atTop (fun _ ↦ β₀)) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ sandwichCovariance
        ((n : ℝ)⁻¹ • ∑ i ∈ range n, DU i (βhat n ω) ω)
        ((n : ℝ)⁻¹ • ∑ i ∈ range n, InnerProductSpace.rankOne ℝ (U i (βhat n ω) ω)
          (U i (βhat n ω) ω))) atTop
      (fun _ ↦ sandwichCovariance (Abar β₀) (Bbar β₀)) :=
  tendstoInMeasure_sandwichCovariance hA
    (tendstoInMeasure_comp_of_tendstoUniformlyOn (Φ := fun n β ω ↦
      (n : ℝ)⁻¹ • ∑ i ∈ range n, DU i β ω) hδ hAbar (by simpa only [dist_eq_norm] using hAunif)
      hcons)
    (tendstoInMeasure_comp_of_tendstoUniformlyOn (Φ := fun n β ω ↦
      (n : ℝ)⁻¹ • ∑ i ∈ range n, InnerProductSpace.rankOne ℝ (U i β ω) (U i β ω)) hδ
      hBbar
      (by simpa only [dist_eq_norm] using hBunif) hcons)

omit [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure P] in
/-- **The empirical sandwich is consistent for the CLT covariance.** Under the hypotheses of
`tendstoInMeasure_empirical_sandwichCovariance`, if the in-probability limit `Bbar β₀` of the
averaged rank-one operators is the meat `B` of the CLT
`tendstoInDistribution_sqrt_smul_sub_sandwich`
(as an operator; for a probability measure `P`, in particular `B` is then self-adjoint), the
empirical sandwich converges in probability to `sandwichCovariance (Abar β₀) B`, the asymptotic
covariance of `tendstoInDistribution_sqrt_smul_sub_sandwich_of_hasFDerivAt`. -/
theorem tendstoInMeasure_empirical_sandwichCovariance_of_eq {U : ℕ → E → Ω → E}
    {DU : ℕ → E → Ω → E →L[ℝ] E} {β₀ : E} {δ : ℝ} (hδ : 0 < δ)
    {Abar Bbar : E → E →L[ℝ] E} {B : E →L[ℝ] E} (hAbar : ContinuousAt Abar β₀)
    (hBbar : ContinuousAt Bbar β₀) (hBB : Bbar β₀ = B) (hA : IsUnit (Abar β₀))
    (hAunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ β ∈ Metric.ball β₀ δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DU i β ω - Abar β‖}) atTop (𝓝 0))
    (hBunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ β ∈ Metric.ball β₀ δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, InnerProductSpace.rankOne ℝ (U i β ω) (U i β ω) -
        Bbar β‖}) atTop (𝓝 0))
    {βhat : ℕ → Ω → E} (hcons : TendstoInMeasure P βhat atTop (fun _ ↦ β₀)) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ sandwichCovariance
        ((n : ℝ)⁻¹ • ∑ i ∈ range n, DU i (βhat n ω) ω)
        ((n : ℝ)⁻¹ • ∑ i ∈ range n, InnerProductSpace.rankOne ℝ (U i (βhat n ω) ω)
          (U i (βhat n ω) ω))) atTop
      (fun _ ↦ sandwichCovariance (Abar β₀) B) :=
  hBB ▸ tendstoInMeasure_empirical_sandwichCovariance hδ hAbar hBbar hA hAunif hBunif hcons

/-- **GEE asymptotic normality from differentiable cluster scores.** The combination of
`linearization_of_hasFDerivAt` and `tendstoInDistribution_sqrt_smul_sub_sandwich`: if the cluster
scores are differentiable near `β₀`, their averaged Jacobian converges uniformly near `β₀` in
probability to a sensitivity function `Abar` continuous at `β₀` with `Abar β₀` invertible, the
estimator is a consistent root of the estimating equation with probability tending to one, and
the Lindeberg and meat hypotheses hold at `β₀`, then
`√n • (βhat n - β₀) → N(0, sandwichCovariance (Abar β₀) B)` in distribution. -/
theorem tendstoInDistribution_sqrt_smul_sub_sandwich_of_hasFDerivAt {U : ℕ → E → Ω → E}
    {DU : ℕ → E → Ω → E →L[ℝ] E} {β₀ : E} {δ : ℝ} (hδ : 0 < δ)
    (hdiff : ∀ i ω, ∀ β ∈ Metric.ball β₀ δ, HasFDerivAt (fun b ↦ U i b ω) (DU i β ω) β)
    {Abar : E → E →L[ℝ] E} (hAbar : ContinuousAt Abar β₀) (hA : IsUnit (Abar β₀))
    (hunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ β ∈ Metric.ball β₀ δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DU i β ω - Abar β‖}) atTop (𝓝 0))
    {B : E →L[ℝ] E}
    (hmeas : ∀ k, Measurable (U k β₀)) (hindep : iIndepFun (fun k ↦ U k β₀) P)
    (hmean : ∀ k, ∫ ω, U k β₀ ω ∂P = 0) (hL2 : ∀ k, MemLp (U k β₀) 2 P)
    (hvar : ∀ t, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ ω, ⟪U k β₀ ω, t⟫ ^ 2 ∂P)
      atTop (𝓝 ⟪B t, t⟫))
    (hL : ∀ t, LindebergConditionTriangular (fun n k ω ↦ (√n)⁻¹ * ⟪U k β₀ ω, t⟫) P)
    {βhat : ℕ → Ω → E} (hβ : ∀ n, AEMeasurable (βhat n) P)
    (hcons : TendstoInMeasure P βhat atTop (fun _ ↦ β₀))
    (hroot : Tendsto (fun n ↦ P {ω | ∑ i ∈ range n, U i (βhat n ω) ω ≠ 0}) atTop (𝓝 0))
    {W : Ω' → E} (hW : AEMeasurable W P')
    (hWlaw : ∀ t, HasLaw (fun ω ↦ ⟪W ω, t⟫)
      (gaussianReal 0 (⟪sandwichCovariance (Abar β₀) B t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n • (βhat n ω - β₀)) atTop W (fun _ ↦ P) P' :=
  tendstoInDistribution_sqrt_smul_sub_sandwich hA hmeas hindep hmean hL2 hvar hL hβ hroot
    (linearization_of_hasFDerivAt hδ hdiff hAbar hunif hcons) hW hWlaw

/-! ### Lindeberg condition for identically distributed clusters -/

omit [FiniteDimensional ℝ E] [IsProbabilityMeasure P] in
/-- **Identically distributed clusters satisfy the cluster Lindeberg condition (proved
input).** If the cluster scores `U k` all have the law of a square-integrable `U 0`, then for
every direction `t` the projected array `(√n)⁻¹ ⟪U k, t⟫`, `k < n`, satisfies
`LindebergConditionTriangular`: its Lindeberg sum is `E[⟪U 0, t⟫² 𝟙{ε √n < |⟪U 0, t⟫|}]`,
which tends to `0` by dominated convergence. -/
theorem lindebergConditionTriangular_inner_of_identDistrib {U : ℕ → Ω → E}
    (hident : ∀ k, IdentDistrib (U k) (U 0) P P) (hL2 : MemLp (U 0) 2 P) (t : E) :
    LindebergConditionTriangular (fun n k ω ↦ (√n)⁻¹ * ⟪U k ω, t⟫) P := by
  intro ε hε
  have hinner : Measurable fun x : E ↦ ⟪x, t⟫ := (continuous_id.inner continuous_const).measurable
  set Z : Ω → ℝ := fun ω ↦ ⟪U 0 ω, t⟫ with hZ_def
  have hZ : AEMeasurable Z P := hinner.comp_aemeasurable (hident 0).aemeasurable_fst
  set h : ℕ → ℝ → ℝ := fun n z ↦ if ε < |(√n)⁻¹ * z| then ((√n)⁻¹ * z) ^ 2 else 0 with hh_def
  have hh : ∀ n, Measurable (h n) := fun n ↦
    Measurable.ite (measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (measurable_id.const_mul _)))
      ((measurable_id.const_mul _).pow_const 2) measurable_const
  set g : ℕ → ℝ → ℝ := fun n z ↦ if ε * √n < |z| then z ^ 2 else 0 with hg_def
  have hg : ∀ n, Measurable (g n) := fun n ↦
    Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
      (measurable_id.pow_const 2) measurable_const
  -- each Lindeberg term is the same integral of a function of `U 0`
  have hterm : ∀ n k : ℕ, ∫ ω, ((√n)⁻¹ * ⟪U k ω, t⟫) ^ 2 *
      Set.indicator {ω' | ε < |(√n)⁻¹ * ⟪U k ω', t⟫|} 1 ω ∂P = ∫ ω, h n (Z ω) ∂P := by
    intro n k
    have := (((hident k).comp hinner).comp (hh n)).integral_eq
    refine (integral_congr_ae (ae_of_all _ fun ω ↦ ?_)).trans this
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, Function.comp_apply, hh_def]
    split_ifs <;> simp
  have hnh : ∀ n : ℕ, 1 ≤ n → ∀ z, (n : ℝ) * h n z = g n z := by
    intro n hn z
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
    have key : (ε < |(√n)⁻¹ * z|) ↔ (ε * √n < |z|) := by
      rw [abs_mul, abs_inv, abs_of_pos hs, inv_mul_eq_div, lt_div_iff₀ hs]
    simp only [hh_def, hg_def]
    by_cases hz : ε * √n < |z|
    · simp only [key, hz, ↓reduceIte]
      rw [mul_pow, inv_pow, Real.sq_sqrt hn'.le, ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]
    · simp only [key, hz, ↓reduceIte, mul_zero]
  have heq : ∀ᶠ n : ℕ in atTop, ∫ ω, g n (Z ω) ∂P = ∑ k ∈ Finset.range n,
      ∫ ω, ((√n)⁻¹ * ⟪U k ω, t⟫) ^ 2 *
        Set.indicator {ω' | ε < |(√n)⁻¹ * ⟪U k ω', t⟫|} 1 ω ∂P := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun ω ↦ (hnh n hn (Z ω)).symm)
  refine Tendsto.congr' heq ?_
  have hZ2 : Integrable (fun ω ↦ Z ω ^ 2) P := (hL2.inner_const t).integrable_sq
  have hlim : Tendsto (fun n : ℕ ↦ ∫ ω, g n (Z ω) ∂P) atTop (𝓝 (∫ _, (0 : ℝ) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω ↦ Z ω ^ 2)
      (fun n ↦ ((hg n).comp_aemeasurable hZ).aestronglyMeasurable) hZ2
      (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_)
    · simp only [hg_def]
      split_ifs <;> simp [sq_nonneg]
    · have hgrow : Tendsto (fun n : ℕ ↦ ε * √(n : ℝ)) atTop atTop :=
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hgrow.eventually_gt_atTop |Z ω|] with n hn
      simp only [hg_def, not_lt.2 hn.le, ↓reduceIte]
  simpa using hlim

omit [FiniteDimensional ℝ E] [IsProbabilityMeasure P] in
/-- **The norm form of the cluster Lindeberg condition implies the projected form.** The
classical multivariate Lindeberg condition for independent clusters,
`n⁻¹ ∑_{k<n} E[‖U k‖² 𝟙{ε √n < ‖U k‖}] → 0` for every `ε > 0`, implies
`LindebergConditionTriangular` for the projected array `(√n)⁻¹ ⟪U k, t⟫` in every direction
`t`, which is the hypothesis of `tendstoInDistribution_inv_sqrt_smul_sum_of_lindeberg`. -/
theorem lindebergConditionTriangular_inner_of_norm {U : ℕ → Ω → E}
    (hmeas : ∀ k, Measurable (U k)) (hL2 : ∀ k, MemLp (U k) 2 P)
    (hL : ∀ ε > 0, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n,
      ∫ ω, ‖U k ω‖ ^ 2 * Set.indicator {ω' | ε * √n < ‖U k ω'‖} 1 ω ∂P) atTop (𝓝 0))
    (t : E) :
    LindebergConditionTriangular (fun n k ω ↦ (√n)⁻¹ * ⟪U k ω, t⟫) P := by
  intro ε hε
  by_cases ht : t = 0
  · subst ht
    simp
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
  set ε' := ε / ‖t‖ with hε'_def
  have hε' : 0 < ε' := div_pos hε htn
  have hterm : ∀ (n k : ℕ), ∫ ω, ((√n)⁻¹ * ⟪U k ω, t⟫) ^ 2 *
      Set.indicator {ω' | ε < |(√n)⁻¹ * ⟪U k ω', t⟫|} 1 ω ∂P ≤
      ‖t‖ ^ 2 * ((n : ℝ)⁻¹ *
        ∫ ω, ‖U k ω‖ ^ 2 * Set.indicator {ω' | ε' * √n < ‖U k ω'‖} 1 ω ∂P) := by
    intro n k
    rw [← integral_const_mul, ← integral_const_mul]
    have hS : MeasurableSet {ω' | ε' * √n < ‖U k ω'‖} :=
      measurableSet_lt measurable_const (hmeas k).norm
    have hint : Integrable (fun ω ↦ ‖U k ω‖ ^ 2 * Set.indicator {ω' | ε' * √n < ‖U k ω'‖} 1 ω)
        P := by
      have h := ((hL2 k).integrable_norm_pow two_ne_zero).indicator hS
      refine h.congr (ae_of_all _ fun ω ↦ ?_)
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
      split_ifs <;> simp
    refine integral_mono_of_nonneg (ae_of_all _ fun ω ↦ ?_) ((hint.const_mul _).const_mul _)
      (ae_of_all _ fun ω ↦ ?_)
    · exact mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    by_cases hA : ε < |(√n)⁻¹ * ⟪U k ω, t⟫|
    · have hcs : |⟪U k ω, t⟫| ≤ ‖U k ω‖ * ‖t‖ := abs_real_inner_le_norm _ _
      have hn : 0 < √(n : ℝ) := by
        by_contra h0
        have : √(n : ℝ) = 0 := le_antisymm (not_lt.1 h0) (Real.sqrt_nonneg _)
        simp [this] at hA
        linarith
      have hB : ε' * √n < ‖U k ω‖ := by
        rw [abs_mul, abs_inv, abs_of_pos hn, inv_mul_eq_div, lt_div_iff₀ hn] at hA
        rw [hε'_def, div_mul_eq_mul_div, div_lt_iff₀ htn]
        linarith
      simp only [hA, hB, ↓reduceIte, mul_one]
      rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      have hsq : ⟪U k ω, t⟫ ^ 2 ≤ (‖U k ω‖ * ‖t‖) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
      have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg n)
      nlinarith [mul_le_mul_of_nonneg_left hsq hinv]
    · simp only [hA, ↓reduceIte, mul_zero]
      split_ifs <;> positivity
  have hsum : ∀ n : ℕ, ∑ k ∈ Finset.range n, ∫ ω, ((√n)⁻¹ * ⟪U k ω, t⟫) ^ 2 *
      Set.indicator {ω' | ε < |(√n)⁻¹ * ⟪U k ω', t⟫|} 1 ω ∂P ≤
      ‖t‖ ^ 2 * ((n : ℝ)⁻¹ * ∑ k ∈ range n,
        ∫ ω, ‖U k ω‖ ^ 2 * Set.indicator {ω' | ε' * √n < ‖U k ω'‖} 1 ω ∂P) := fun n ↦ by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ ↦ hterm n k
  have hupper := (hL ε' hε').const_mul (‖t‖ ^ 2)
  rw [mul_zero] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun n ↦ ?_) hsum
  exact Finset.sum_nonneg fun k _ ↦ integral_nonneg fun ω ↦
    mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)

end ProbabilityTheory.GEE
