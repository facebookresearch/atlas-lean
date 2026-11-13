/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.AalenJohansenCLT
public import MathlibExt.Probability.Statistics.Survival.ProcessInference

/-!
# Fixed-grid Wald intervals for Kaplan–Meier and Aalen–Johansen

Inferential consequences of the merged fixed-grid joint central limit theorem for the
Kaplan–Meier survival and the Aalen–Johansen cumulative incidences
(`AalenJohansenCLT.tendstoInDistribution_estimator`). For a coordinate `a` of the joint
estimator (the Kaplan–Meier survival `Ŝ(j)` or a cumulative incidence `F̂_c(j)` at a grid index
`j ≤ m`), the asymptotic variance is the variance of the influence coordinate of one subject,
`asymVar μ m a = Var_μ[influence μ m · a]`. The Wald interval with a consistent standard error
`se n → √(asymVar μ m a)` is

  `estimator a ± z · se n / √n`  (`ProcessInference.waldInterval`).

## Nondegeneracy

Every coverage statement assumes the **nondegeneracy condition** `0 < asymVar μ m a` for each
coordinate it covers. Under it the coordinate limit is a nondegenerate centered Gaussian, which
puts no mass on the boundary of the studentized region, so the portmanteau theorem applies. If
`asymVar μ m a = 0` the limit is the point mass at `0`, which charges that boundary, and the
coverage limit is not determined by the central limit theorem; nothing is claimed then (see the
degenerate example in the test file, where coverage is `1` for every sample size while the
nominal level at `z = 0` is `0`).

## Main definitions

* `asymVar μ m a`: the asymptotic variance of the estimator coordinate `a`, the variance under the
  subject law `μ` of the influence coordinate `influence μ m · a`.
* `nominalLevel z`: the standard-normal mass of `[-z, z]`, the nominal level of the two-sided Wald
  interval with critical value `z`.

## Main results

* `exists_tendstoInDistribution_coord`: the scalar limit of one coordinate,
  `√n (estimator a - ajMap m (cellMean μ) a) → N(0, asymVar μ m a)`, derived from the joint theorem.
* `tendsto_coverage_waldInterval_estimator`: for any i.i.d. subject law `μ` with
  `P(min T C ≥ m) ≠ 0` and `0 < asymVar μ m a`, the Wald interval with a consistent standard error
  covers the plug-in limit `ajMap m (cellMean μ) a` with probability tending to `nominalLevel z`.
  `tendsto_coverage_waldInterval_estimator_oracle` is the known-variance case.
* `tendsto_coverage_waldInterval_indepCauseLaw`: under independent censoring the covered quantity
  is the estimand `target pTJ m a`; `tendsto_coverage_kmSurvival_waldInterval` (survival
  `P(T > j)`) and `tendsto_coverage_cumulativeIncidence_waldInterval` (cumulative incidence
  `P(T ≤ j, J = c)`) state the two kinds of coordinates explicitly.
* `tendsto_coverage_gridBand_estimator`: for a finite family `g : ι → Coord k r m` of coordinates
  (a fixed grid of time points, possibly mixing survival and cumulative-incidence coordinates),
  all nondegenerate, the simultaneous Wald band covers all of them with probability tending to
  `P(∀ i, |Y i| ≤ z √(asymVar μ m (g i)))` for the Gaussian joint limit `Y`; this limit lies
  between the Bonferroni bound `1 - card ι · (1 - nominalLevel z)` and `nominalLevel z`.
  `tendsto_coverage_gridBand_indepCauseLaw` centres it at the estimand.

## Scope

Fixed grid and fixed horizon `m` with `P(min T C ≥ m) ≠ 0`, as in the merged joint theorem. The
asymptotic variance is identified as the variance of the influence coordinate; its closed
Greenwood-type form is not derived, and consistency of a variance estimator is a hypothesis
(`TendstoInMeasure`). Critical values with prescribed simultaneous coverage are not constructed.
No convergence in `D[0, τ]` and no continuum band is claimed.

## References

* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Sections IV.3–IV.4 (pointwise confidence intervals for the
  Kaplan–Meier and Aalen–Johansen estimators).
* J. P. Klein and M. L. Moeschberger, *Survival Analysis: Techniques for Censored and Truncated
  Data*, 2nd ed., Springer (2003), Section 4.3 (pointwise confidence intervals for the survival
  function).
* A. W. van der Vaart, *Asymptotic Statistics* (1998), Section 2.1 and Lemma 2.11 (Slutsky and the
  portmanteau theorem).
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.FixedGridIntervals

open MeasureTheory ProbabilityTheory Filter Finset Topology
open MathlibExt.Probability.Statistics.AalenJohansenCLT
open MathlibExt.Probability.Statistics.ProcessInference
open MathlibExt.Probability.Statistics.Censoring MathlibExt.Probability.Statistics.CompetingRisks
open MathlibExt.Probability.Statistics.SurvivalConsistency

variable {k r : ℕ}

/-- The **asymptotic variance** of the coordinate `a` of the joint Kaplan–Meier / Aalen–Johansen
estimator at the horizon `m`: the variance, under the subject law `μ`, of the influence
coordinate `influence μ m w a`. It is the variance of the coordinate `a` of the joint Gaussian
limit (`exists_tendstoInDistribution_coord`). -/
noncomputable def asymVar (μ : Measure ((Fin k × Fin r) × Fin k)) (m : Fin k)
    (a : Coord k r m) : ℝ :=
  Var[fun w => influence μ m w a; μ]

theorem asymVar_nonneg (μ : Measure ((Fin k × Fin r) × Fin k)) (m : Fin k) (a : Coord k r m) :
    0 ≤ asymVar μ m a :=
  variance_nonneg _ _

/-- The **nominal level** of the two-sided Wald interval with critical value `z`: the
standard-normal mass of `[-z, z]`. -/
noncomputable def nominalLevel (z : ℝ) : ℝ :=
  (gaussianReal 0 1).real (Set.Icc (-z) z)

theorem nominalLevel_nonneg (z : ℝ) : 0 ≤ nominalLevel z := measureReal_nonneg

theorem nominalLevel_le_one (z : ℝ) : nominalLevel z ≤ 1 := measureReal_le_one

/-- The Wald interval with standard error `σ / √n` is the closed interval of half-width
`z σ / √n` around the estimate. -/
theorem waldInterval_div_sqrt_eq (est σ z : ℝ) (n : ℕ) :
    waldInterval est (σ / √(n : ℝ)) z =
      Set.Icc (est - z * σ / √(n : ℝ)) (est + z * σ / √(n : ℝ)) := by
  simp only [waldInterval, mul_div_assoc]

/-- `√` of the nonnegative part of a nonnegative real is its `√`. -/
private theorem sqrt_coe_toNNReal {x : ℝ} (hx : 0 ≤ x) : √((x.toNNReal : ℝ)) = √x := by
  rw [Real.coe_toNNReal _ hx]

private theorem toNNReal_ne_zero {x : ℝ} (hx : 0 < x) : x.toNNReal ≠ 0 := by
  simpa [Real.toNNReal_eq_zero, not_le] using hx

/-- A constant sequence converges in probability to its value. -/
private theorem tendstoInMeasure_const {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {E : Type*} [PseudoMetricSpace E] (c : E) :
    TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => c) atTop (fun _ => c) :=
  tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (ae_of_all _ fun _ => tendsto_const_nhds)

section Limits

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure ((Fin k × Fin r) × Fin k)} {W : ℕ → Ω → (Fin k × Fin r) × Fin k}

omit [IsProbabilityMeasure P] in
/-- The variance of a function of the first subject is its variance under the subject law. -/
theorem variance_comp_eq (hlaw : HasLaw (W 0) μ P) (f : (Fin k × Fin r) × Fin k → ℝ) :
    Var[fun ω => f (W 0 ω); P] = Var[f; μ] := by
  rw [← hlaw.map_eq, variance_map Measurable.of_discrete.aemeasurable hlaw.aemeasurable]
  rfl

/-- **The scalar limit of one coordinate.** Under the hypotheses of the merged joint theorem
(i.i.d. subjects with law `μ`, `P(min T C ≥ m) ≠ 0`), for every coordinate `a`,
`√n (estimator a - ajMap m (cellMean μ) a)` converges in distribution to a centered Gaussian of
variance `asymVar μ m a`. -/
theorem exists_tendstoInDistribution_coord (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) μ P) (m : Fin k) (hm : causeAtRiskMass μ m ≠ 0)
    (a : Coord k r m) :
    ∃ Z : EuclideanSpace ℝ (Cell k r) → ℝ,
      HasLaw Z (gaussianReal 0 (asymVar μ m a).toNNReal)
        (stdGaussian (EuclideanSpace ℝ (Cell k r))) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) *
          (estimator m (empiricalCauseData W n ω) a - ajMap m (cellMean μ) a))
        atTop Z (fun _ => P) (stdGaussian (EuclideanSpace ℝ (Cell k r))) := by
  classical
  obtain ⟨Y, -, hY, hconv⟩ := tendstoInDistribution_estimator hind hlaw m hm
  refine ⟨fun z => Y z a, ?_, ?_⟩
  · have h := hY (Pi.single a 1)
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
      ite_true] at h
    rwa [variance_comp_eq (hlaw 0) (fun w => influence μ m w a)] at h
  · exact (hconv.continuous_comp (continuous_apply a)).congr
      (fun n => ae_of_all _ fun ω => rfl) (ae_of_all _ fun _ => rfl)

/-- **Pointwise asymptotic coverage of the fixed-grid Wald interval.** Let the subjects be
i.i.d. with law `μ` (no independence of `(T, J)` and `C` assumed), with `P(min T C ≥ m) ≠ 0`, and
let `a` be a coordinate of the joint estimator (Kaplan–Meier survival or a cumulative incidence at
a grid index `j ≤ m`) satisfying the **nondegeneracy condition** `0 < asymVar μ m a`. If `se n`
is a consistent estimator of `√(asymVar μ m a)`, the Wald interval
`estimator a ± z · se n / √n` covers the plug-in limit `ajMap m (cellMean μ) a` with probability
tending to the nominal level `nominalLevel z`. -/
theorem tendsto_coverage_waldInterval_estimator (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) μ P) (m : Fin k) (hm : causeAtRiskMass μ m ≠ 0)
    (a : Coord k r m) (hv : 0 < asymVar μ m a) (z : ℝ) {se : ℕ → Ω → ℝ}
    (hse : TendstoInMeasure P se atTop (fun _ => √(asymVar μ m a)))
    (hse_meas : ∀ n, AEMeasurable (se n) P) :
    Tendsto (fun n : ℕ => P.real {ω | ajMap m (cellMean μ) a ∈
        waldInterval (estimator m (empiricalCauseData W n ω) a) (se n ω / √(n : ℝ)) z})
      atTop (𝓝 (nominalLevel z)) := by
  obtain ⟨Z, hZ, hconv⟩ := exists_tendstoInDistribution_coord hind hlaw m hm a
  refine tendsto_coverage_waldInterval (toNNReal_ne_zero hv) z hconv hZ ?_ hse_meas
  rwa [sqrt_coe_toNNReal hv.le]

/-- **Known-variance (oracle) Wald interval.** Under the hypotheses of
`tendsto_coverage_waldInterval_estimator`, the interval
`estimator a ± z · √(asymVar μ m a) / √n` covers `ajMap m (cellMean μ) a` with probability
tending to `nominalLevel z`. -/
theorem tendsto_coverage_waldInterval_estimator_oracle (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) μ P) (m : Fin k) (hm : causeAtRiskMass μ m ≠ 0)
    (a : Coord k r m) (hv : 0 < asymVar μ m a) (z : ℝ) :
    Tendsto (fun n : ℕ => P.real {ω | ajMap m (cellMean μ) a ∈
        waldInterval (estimator m (empiricalCauseData W n ω) a)
          (√(asymVar μ m a) / √(n : ℝ)) z})
      atTop (𝓝 (nominalLevel z)) :=
  tendsto_coverage_waldInterval_estimator hind hlaw m hm a hv z
    (tendstoInMeasure_const _) (fun _ => aemeasurable_const)

/-- **Simultaneous fixed-grid Wald band.** Let `g : ι → Coord k r m` be a finite family of
coordinates of the joint estimator (for instance the Kaplan–Meier survival at a fixed grid of
time points, or a mix of survival and cumulative-incidence coordinates), all satisfying the
nondegeneracy condition `0 < asymVar μ m (g i)`. Then there is a centered Gaussian vector `Y`
with `Y i ∼ N(0, asymVar μ m (g i))` such that, for every critical value `z` and every
consistent standard-error vector `se n → (√(asymVar μ m (g i)))_i`, the band
`estimator (g i) ± z · se n i / √n` covers all `ajMap m (cellMean μ) (g i)` simultaneously with
probability tending to `P(∀ i, |Y i| ≤ z √(asymVar μ m (g i)))`. That limit is at most the
nominal level `nominalLevel z` (for nonempty `ι`) and at least the Bonferroni bound
`1 - card ι · (1 - nominalLevel z)`. -/
theorem tendsto_coverage_gridBand_estimator (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) μ P) (m : Fin k) (hm : causeAtRiskMass μ m ≠ 0)
    {ι : Type*} [Fintype ι] (g : ι → Coord k r m) (hv : ∀ i, 0 < asymVar μ m (g i)) :
    ∃ Y : EuclideanSpace ℝ (Cell k r) → ι → ℝ,
      HasGaussianLaw Y (stdGaussian (EuclideanSpace ℝ (Cell k r))) ∧
      (∀ i, HasLaw (fun x => Y x i) (gaussianReal 0 (asymVar μ m (g i)).toNNReal)
        (stdGaussian (EuclideanSpace ℝ (Cell k r)))) ∧
      (∀ (z : ℝ) {se : ℕ → Ω → ι → ℝ},
        TendstoInMeasure P se atTop (fun _ i => √(asymVar μ m (g i))) →
        (∀ n, AEMeasurable (se n) P) →
        Tendsto (fun n : ℕ => P.real {ω | (fun i => ajMap m (cellMean μ) (g i)) ∈
            gridBand (fun i => estimator m (empiricalCauseData W n ω) (g i))
              (fun i => se n ω i / √(n : ℝ)) z})
          atTop (𝓝 ((stdGaussian (EuclideanSpace ℝ (Cell k r))).real
            {x | ∀ i, |Y x i| ≤ z * √(asymVar μ m (g i))}))) ∧
      (∀ z : ℝ, Nonempty ι → (stdGaussian (EuclideanSpace ℝ (Cell k r))).real
        {x | ∀ i, |Y x i| ≤ z * √(asymVar μ m (g i))} ≤ nominalLevel z) ∧
      (∀ z : ℝ, 1 - Fintype.card ι * (1 - nominalLevel z) ≤
        (stdGaussian (EuclideanSpace ℝ (Cell k r))).real
          {x | ∀ i, |Y x i| ≤ z * √(asymVar μ m (g i))}) := by
  classical
  obtain ⟨Y, hYg, hY, hconv⟩ := tendstoInDistribution_estimator hind hlaw m hm
  let L : (Coord k r m → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (g i)
  set v : ι → NNReal := fun i => (asymVar μ m (g i)).toNNReal with hvdef
  have hv0 : ∀ i, v i ≠ 0 := fun i => toNNReal_ne_zero (hv i)
  have hsq : ∀ i, √((v i : ℝ)) = √(asymVar μ m (g i)) := fun i => sqrt_coe_toNNReal (hv i).le
  have hYi : ∀ i, HasLaw (fun x => L (Y x) i) (gaussianReal 0 (v i))
      (stdGaussian (EuclideanSpace ℝ (Cell k r))) := fun i => by
    have h := hY (Pi.single (g i) 1)
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
      ite_true] at h
    rwa [variance_comp_eq (hlaw 0) (fun w => influence μ m w (g i))] at h
  have hlim : TendstoInDistribution
      (fun (n : ℕ) ω i => √(n : ℝ) * (estimator m (empiricalCauseData W n ω) (g i) -
        ajMap m (cellMean μ) (g i)))
      atTop (fun x => L (Y x)) (fun _ => P) (stdGaussian (EuclideanSpace ℝ (Cell k r))) :=
    (hconv.continuous_comp L.continuous).congr (fun n => ae_of_all _ fun ω => rfl)
      (ae_of_all _ fun _ => rfl)
  refine ⟨fun x => L (Y x), hYg.map L, hYi, fun z se hse hse_meas => ?_, fun z ⟨i⟩ => ?_,
    fun z => ?_⟩
  · have h := tendsto_coverage_gridBand hv0 z hlim hYi
      (by simpa only [hsq] using hse) hse_meas
    simpa only [hsq] using h
  · have h := gridBand_limit_le_pointwise hv0 hYi z i
    simpa only [hsq, nominalLevel] using h
  · have h := one_sub_card_mul_le_gridBand_limit hv0 hYi z
    simpa only [hsq, nominalLevel] using h

end Limits

/-! ### Independent censoring: coverage of the estimand -/

section IndependentCensoring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℕ → Ω → (Fin k × Fin r) × Fin k}

/-- **Pointwise Wald coverage of the estimand under independent censoring.** For i.i.d. subjects
with law `indepCauseLaw pTJ pC`, `P(min T C ≥ m) ≠ 0`, and a nondegenerate coordinate `a`, the
Wald interval with a consistent standard error covers the estimand `target pTJ m a` (the survival
`P(T > j)` or the cumulative incidence `P(T ≤ j, J = c)`) with probability tending to
`nominalLevel z`. -/
theorem tendsto_coverage_waldInterval_indepCauseLaw (pTJ : PMF (Fin k × Fin r))
    (pC : PMF (Fin k)) (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) (indepCauseLaw pTJ pC) P) (m : Fin k)
    (hm : causeAtRiskMass (indepCauseLaw pTJ pC) m ≠ 0) (a : Coord k r m)
    (hv : 0 < asymVar (indepCauseLaw pTJ pC) m a) (z : ℝ) {se : ℕ → Ω → ℝ}
    (hse : TendstoInMeasure P se atTop (fun _ => √(asymVar (indepCauseLaw pTJ pC) m a)))
    (hse_meas : ∀ n, AEMeasurable (se n) P) :
    Tendsto (fun n : ℕ => P.real {ω | target pTJ m a ∈
        waldInterval (estimator m (empiricalCauseData W n ω) a) (se n ω / √(n : ℝ)) z})
      atTop (𝓝 (nominalLevel z)) := by
  rw [← ajMap_cellMean_indepCauseLaw pTJ pC m hm]
  exact tendsto_coverage_waldInterval_estimator hind hlaw m hm a hv z hse hse_meas

/-- **Kaplan–Meier Wald interval at a grid time.** Under independent censoring with
`P(min T C ≥ m) ≠ 0`, for a grid index `j ≤ m` whose Kaplan–Meier coordinate is nondegenerate,
the interval `Ŝ(j) ± z · se n / √n` covers the survival `P(T > j)` with probability tending to
`nominalLevel z`. -/
theorem tendsto_coverage_kmSurvival_waldInterval (pTJ : PMF (Fin k × Fin r))
    (pC : PMF (Fin k)) (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) (indepCauseLaw pTJ pC) P) (m : Fin k)
    (hm : causeAtRiskMass (indepCauseLaw pTJ pC) m ≠ 0) (j : Fin k) (hj : j ≤ m)
    (hv : 0 < asymVar (indepCauseLaw pTJ pC) m (none, ⟨j, hj⟩)) (z : ℝ) {se : ℕ → Ω → ℝ}
    (hse : TendstoInMeasure P se atTop
      (fun _ => √(asymVar (indepCauseLaw pTJ pC) m (none, ⟨j, hj⟩))))
    (hse_meas : ∀ n, AEMeasurable (se n) P) :
    Tendsto (fun n : ℕ => P.real {ω | (PMF.map Prod.fst pTJ).toMeasure.real {t | j < t} ∈
        waldInterval ((empiricalCauseData W n ω).toCensoredData.kmSurvival ((j : ℕ) : ℝ))
          (se n ω / √(n : ℝ)) z})
      atTop (𝓝 (nominalLevel z)) :=
  tendsto_coverage_waldInterval_indepCauseLaw pTJ pC hind hlaw m hm (none, ⟨j, hj⟩) hv z hse
    hse_meas

/-- **Aalen–Johansen Wald interval at a grid time.** Under independent censoring with
`P(min T C ≥ m) ≠ 0`, for a cause `c` and a grid index `j ≤ m` whose cumulative-incidence
coordinate is nondegenerate, the interval `F̂_c(j) ± z · se n / √n` covers the cumulative incidence
`P(T ≤ j, J = c)` with probability tending to `nominalLevel z`. -/
theorem tendsto_coverage_cumulativeIncidence_waldInterval (pTJ : PMF (Fin k × Fin r))
    (pC : PMF (Fin k)) (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) (indepCauseLaw pTJ pC) P) (m : Fin k)
    (hm : causeAtRiskMass (indepCauseLaw pTJ pC) m ≠ 0) (c : Fin r) (j : Fin k) (hj : j ≤ m)
    (hv : 0 < asymVar (indepCauseLaw pTJ pC) m (some c, ⟨j, hj⟩)) (z : ℝ) {se : ℕ → Ω → ℝ}
    (hse : TendstoInMeasure P se atTop
      (fun _ => √(asymVar (indepCauseLaw pTJ pC) m (some c, ⟨j, hj⟩))))
    (hse_meas : ∀ n, AEMeasurable (se n) P) :
    Tendsto (fun n : ℕ => P.real {ω | pTJ.toMeasure.real {x | x.1 ≤ j ∧ x.2 = c} ∈
        waldInterval ((empiricalCauseData W n ω).cumulativeIncidence c ((j : ℕ) : ℝ))
          (se n ω / √(n : ℝ)) z})
      atTop (𝓝 (nominalLevel z)) :=
  tendsto_coverage_waldInterval_indepCauseLaw pTJ pC hind hlaw m hm (some c, ⟨j, hj⟩) hv z hse
    hse_meas

/-- **Simultaneous fixed-grid Wald band for the estimand under independent censoring.** The
band of `tendsto_coverage_gridBand_estimator` covers the estimand `target pTJ m (g i)` at all
`i` simultaneously with probability tending to `P(∀ i, |Y i| ≤ z √(asymVar (g i)))`, which lies
between `1 - card ι · (1 - nominalLevel z)` and `nominalLevel z`. -/
theorem tendsto_coverage_gridBand_indepCauseLaw (pTJ : PMF (Fin k × Fin r))
    (pC : PMF (Fin k)) (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) (indepCauseLaw pTJ pC) P) (m : Fin k)
    (hm : causeAtRiskMass (indepCauseLaw pTJ pC) m ≠ 0)
    {ι : Type*} [Fintype ι] (g : ι → Coord k r m)
    (hv : ∀ i, 0 < asymVar (indepCauseLaw pTJ pC) m (g i)) :
    ∃ Y : EuclideanSpace ℝ (Cell k r) → ι → ℝ,
      HasGaussianLaw Y (stdGaussian (EuclideanSpace ℝ (Cell k r))) ∧
      (∀ i, HasLaw (fun x => Y x i)
        (gaussianReal 0 (asymVar (indepCauseLaw pTJ pC) m (g i)).toNNReal)
        (stdGaussian (EuclideanSpace ℝ (Cell k r)))) ∧
      (∀ (z : ℝ) {se : ℕ → Ω → ι → ℝ},
        TendstoInMeasure P se atTop
          (fun _ i => √(asymVar (indepCauseLaw pTJ pC) m (g i))) →
        (∀ n, AEMeasurable (se n) P) →
        Tendsto (fun n : ℕ => P.real {ω | (fun i => target pTJ m (g i)) ∈
            gridBand (fun i => estimator m (empiricalCauseData W n ω) (g i))
              (fun i => se n ω i / √(n : ℝ)) z})
          atTop (𝓝 ((stdGaussian (EuclideanSpace ℝ (Cell k r))).real
            {x | ∀ i, |Y x i| ≤ z * √(asymVar (indepCauseLaw pTJ pC) m (g i))}))) ∧
      (∀ z : ℝ, Nonempty ι → (stdGaussian (EuclideanSpace ℝ (Cell k r))).real
        {x | ∀ i, |Y x i| ≤ z * √(asymVar (indepCauseLaw pTJ pC) m (g i))} ≤
          nominalLevel z) ∧
      (∀ z : ℝ, 1 - Fintype.card ι * (1 - nominalLevel z) ≤
        (stdGaussian (EuclideanSpace ℝ (Cell k r))).real
          {x | ∀ i, |Y x i| ≤ z * √(asymVar (indepCauseLaw pTJ pC) m (g i))}) := by
  have h := tendsto_coverage_gridBand_estimator hind hlaw m hm g hv
  rwa [ajMap_cellMean_indepCauseLaw pTJ pC m hm] at h

end IndependentCensoring

end MathlibExt.Probability.Statistics.FixedGridIntervals
