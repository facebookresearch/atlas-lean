/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.Consistency
public import MathlibExt.Probability.Statistics.Survival.CompetingRisks
public import MathlibExt.Probability.Statistics.MultivariateCLT
public import MathlibExt.Probability.Statistics.DeltaMethod

/-!
# Fixed-grid joint central limit theorem for Aalen–Johansen and Kaplan–Meier

Subjects `i = 0, 1, …` have event time, cause and censoring time `Wᵢ = ((Tᵢ, Jᵢ), Cᵢ)` on the grid
`Fin k` with `r` causes, i.i.d. with law `μ`; the grouped data of the first `n` subjects are
`empiricalCauseData W n ω` (from `Survival/Consistency.lean`). For a horizon `m : Fin k`, the joint
estimator `estimator m D` collects, for every grid index `j ≤ m`, the cause-blind Kaplan–Meier
survival `Ŝ(j)` and the Aalen–Johansen cumulative incidences `F̂_c(j)` of all causes `c`.

## Main definitions

* `cellVector w`: the indicator vector of one subject in the cells "failure from cause `c` at `j`"
  and "at risk at `j`"; `cellMean μ` is its mean (`integral_cellVector`).
* `ajMap m u`: the rational map of the cell vector giving `(Ŝ(j), F̂_c(j))_{c, j ≤ m}`; it is
  scale invariant, so the estimator is `ajMap m` of the empirical mean cell vector
  (`ajMap_empiricalMean`).
* `influence μ m w`: the derivative of `ajMap m` at `cellMean μ` applied to `cellVector w`.
* `target pTJ m`: the estimand `(P(T > j), P(T ≤ j, J = c))_{c, j ≤ m}`.

## Main results

* `exists_tendstoInDistribution_empiricalMean`: the cell-count multivariate CLT
  `√n (empiricalMean - cellMean μ) → A`, from `tendstoInDistribution_inv_sqrt_smul_sum_sub`.
* `exists_tendstoInDistribution_estimator`, `tendstoInDistribution_estimator`: **joint CLT** for
  any i.i.d. law `μ` with `P(min T C ≥ m) ≠ 0`: `√n (estimator - ajMap m (cellMean μ))` converges in
  distribution to a Gaussian vector `Y` whose linear combinations `∑ₐ sₐ Yₐ` have variance
  `Var[∑ₐ sₐ influenceₐ]`, by the finite-dimensional delta method.
* `covariance_limit`: the full covariance matrix, `Cov(Yₐ, Y_b) = Cov(influenceₐ, influence_b)`.
* `ajMap_cellMean_indepCauseLaw`: in the independent-censoring model `indepCauseLaw pTJ pC` the
  plug-in limit is the estimand `target pTJ m`.
* `tendstoInDistribution_estimator_indepCauseLaw`: the joint CLT centered at
  `(P(T > j), P(T ≤ j, J = c))`.
* `tendstoInDistribution_kmSurvival_indepCauseLaw`: the Kaplan–Meier marginal at one grid time,
  derived from the joint theorem.

## Scope

Fixed grid and fixed horizon `m` inside the support of the observed follow-up
(`P(min T C ≥ m) ≠ 0`). The limit covariance is identified as the covariance of the influence
vector `fderiv (ajMap m) (cellMean μ) (cellVector W₀)`; the closed-form Greenwood-type
expressions for its entries are not derived. No convergence in `D[0, τ]`, no uniformity in `m`,
and nothing beyond the support of `C`.

## References

* O. O. Aalen and S. Johansen, *An empirical transition matrix for non-homogeneous Markov chains
  based on censored observations*, Scand. J. Statist. 5 (1978), 141–150.
* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Section IV.4.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), Theorem 3.1 (delta method).
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.AalenJohansenCLT

open MeasureTheory ProbabilityTheory Filter Finset Topology RealInnerProductSpace
open MathlibExt.Probability.Statistics.Censoring MathlibExt.Probability.Statistics.KaplanMeier
open MathlibExt.Probability.Statistics.CompetingRisks
open MathlibExt.Probability.Statistics.SurvivalConsistency

variable {k r : ℕ}

/-- The cells of one subject's grouped competing-risks record: `Sum.inl (j, c)` is the cell
"observed failure from cause `c` at grid index `j`", and `Sum.inr j` is the cell "at risk at grid
index `j`". -/
abbrev Cell (k r : ℕ) := (Fin k × Fin r) ⊕ Fin k

/-- The coordinates of the joint estimator up to the horizon `m`: `(none, j)` is the
Kaplan–Meier survival at grid index `j ≤ m`, and `(some c, j)` is the Aalen–Johansen cumulative
incidence of cause `c` at `j`. -/
abbrev Coord (k r : ℕ) (m : Fin k) := Option (Fin r) × {j : Fin k // j ≤ m}

/-- The cell indicator vector of one subject `w = ((T, J), C)`: the coordinate `Sum.inl (j, c)`
is `1[min T C = j, T ≤ C, J = c]` and the coordinate `Sum.inr j` is `1[min T C ≥ j]`. Summing it
over subjects gives the cause-specific event counts and the at-risk counts. -/
noncomputable def cellVector (w : (Fin k × Fin r) × Fin k) : EuclideanSpace ℝ (Cell k r) :=
  WithLp.toLp 2 fun
    | Sum.inl (j, c) => if min w.1.1 w.2 = j ∧ w.1.1 ≤ w.2 ∧ w.1.2 = c then 1 else 0
    | Sum.inr j => if j ≤ min w.1.1 w.2 then 1 else 0

/-- The mean of the cell indicator vector under a law `μ` of `((T, J), C)`: the cause-specific
observed event masses `causeEventMass μ j c` and the at-risk masses `causeAtRiskMass μ j`. -/
noncomputable def cellMean (μ : Measure ((Fin k × Fin r) × Fin k)) :
    EuclideanSpace ℝ (Cell k r) :=
  WithLp.toLp 2 fun
    | Sum.inl (j, c) => causeEventMass μ j c
    | Sum.inr j => causeAtRiskMass μ j

/-- The Kaplan–Meier factor `1 - (∑_c u_{l,c}) / u_l` of a cell vector `u` at grid index `l`. -/
noncomputable def factor (u : EuclideanSpace ℝ (Cell k r)) (l : Fin k) : ℝ :=
  1 - (∑ c, u (Sum.inl (l, c))) / u (Sum.inr l)

/-- The **Aalen–Johansen map** on cell vectors, up to the horizon `m`: coordinate `(none, j)` is
the product-limit survival `∏_{l ≤ j} factor u l`, and coordinate `(some c, j)` is the cumulative
incidence `∑_{l ≤ j} (∏_{i < l} factor u i) · u_{l,c} / u_l`. The ratios are scale invariant, so
on the empirical mean cell vector it gives the Kaplan–Meier and Aalen–Johansen estimates
(`map_empiricalMean`). -/
noncomputable def ajMap (m : Fin k) (u : EuclideanSpace ℝ (Cell k r)) : Coord k r m → ℝ
  | (none, j) => ∏ l with l ≤ j.1, factor u l
  | (some c, j) => ∑ l with l ≤ j.1, (∏ i with i < l, factor u i) *
      (u (Sum.inl (l, c)) / u (Sum.inr l))

/-- The joint estimator up to the horizon `m` from grouped competing-risks data `D`: coordinate
`(none, j)` is the cause-blind Kaplan–Meier survival at `time j`, and coordinate `(some c, j)` is
the Aalen–Johansen cumulative incidence of cause `c` at `time j`. -/
noncomputable def estimator (m : Fin k) (D : CompetingRiskData k r) : Coord k r m → ℝ
  | (none, j) => D.toCensoredData.kmSurvival (D.time j)
  | (some c, j) => D.cumulativeIncidence c (D.time j)

/-! ### Regularity of the Aalen–Johansen map -/

/-- The Aalen–Johansen map is measurable (it is built from coordinates by finitely many sums,
products and divisions). -/
theorem measurable_ajMap (m : Fin k) : Measurable (ajMap (r := r) m) := by
  have hcoord : ∀ i : Cell k r, Measurable fun u : EuclideanSpace ℝ (Cell k r) => (u i : ℝ) :=
    fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
  have hfac : ∀ l, Measurable fun u : EuclideanSpace ℝ (Cell k r) => factor u l := by
    intro l
    simp only [factor]
    fun_prop
  refine measurable_pi_iff.2 fun a => ?_
  rcases a with ⟨_ | c, j⟩
  · simp only [ajMap]
    fun_prop
  · simp only [ajMap]
    fun_prop

/-- The Aalen–Johansen map is differentiable at every cell vector whose at-risk coordinates up to
the horizon `m` are nonzero. -/
theorem differentiableAt_ajMap (m : Fin k) {u : EuclideanSpace ℝ (Cell k r)}
    (hu : ∀ l ≤ m, u (Sum.inr l) ≠ 0) : DifferentiableAt ℝ (ajMap m) u := by
  have hcoord : ∀ (i : Cell k r) (v : EuclideanSpace ℝ (Cell k r)),
      DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Cell k r) => (u i : ℝ)) v :=
    fun i v => (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt
  have hfac : ∀ l ≤ m,
      DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Cell k r) => factor u l) u := by
    intro l hl
    have := hu l hl
    simp only [factor]
    fun_prop (disch := assumption)
  have hprod : ∀ s : Finset (Fin k), (∀ l ∈ s, l ≤ m) →
      DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Cell k r) => ∏ l ∈ s, factor u l) u := by
    classical
    intro s hs
    exact (HasFDerivAt.finsetProd (g := fun l u => factor u l)
      fun l hl => (hfac l (hs l hl)).hasFDerivAt).differentiableAt
  rw [differentiableAt_pi]
  rintro ⟨_ | c, j⟩
  · exact hprod _ fun l hl => le_trans (by simpa using hl) j.2
  · simp only [ajMap]
    refine DifferentiableAt.fun_sum fun l hl => ?_
    have hl : l ≤ m := le_trans (by simpa using hl) j.2
    have hul := hu l hl
    have hp := hprod (filter (· < l) univ) fun i hi => le_trans (by simpa using hi : i < l).le hl
    fun_prop (disch := assumption)

/-- The Aalen–Johansen map is invariant under rescaling the cell vector by a nonzero scalar. -/
theorem ajMap_smul (m : Fin k) {a : ℝ} (ha : a ≠ 0) (u : EuclideanSpace ℝ (Cell k r)) :
    ajMap m (a • u) = ajMap m u := by
  have hratio : ∀ x y : ℝ, (a * x) / (a * y) = x / y := fun x y => mul_div_mul_left x y ha
  have hfac : ∀ l, factor (a • u) l = factor u l := fun l => by
    simp only [factor, PiLp.smul_apply, smul_eq_mul, ← mul_sum, hratio]
  funext a
  rcases a with ⟨_ | c, j⟩
  · simp only [ajMap, hfac]
  · simp only [ajMap, hfac, PiLp.smul_apply, smul_eq_mul, hratio]

/-! ### The estimator as a function of the empirical cell means -/

section Empirical

variable {Ω : Type*}

/-- The empirical mean `n⁻¹ ∑_{i < n} cellVector (W i ω)` of the cell vectors of the first `n`
subjects: the event and at-risk proportions `d_{j,c} / n` and `Y_j / n`. -/
noncomputable def empiricalMean (W : ℕ → Ω → (Fin k × Fin r) × Fin k) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Cell k r) :=
  (n : ℝ)⁻¹ • ∑ i ∈ range n, cellVector (W i ω)

private lemma sum_range_ite_eq_card (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    ∑ i ∈ range n, (if p i then (1 : ℝ) else 0) = ((#{i : Fin n | p i} : ℕ) : ℝ) := by
  rw [natCast_card_filter, ← Fin.sum_univ_eq_sum_range (fun i => if p i then (1 : ℝ) else 0) n]

/-- The event coordinates of the summed cell vectors are the cause-specific event counts. -/
theorem sum_cellVector_inl (W : ℕ → Ω → (Fin k × Fin r) × Fin k) (n : ℕ) (ω : Ω) (j : Fin k)
    (c : Fin r) :
    (∑ i ∈ range n, cellVector (W i ω)) (Sum.inl (j, c)) =
      (empiricalCauseData W n ω).events j c := by
  classical
  simp only [WithLp.ofLp_sum, Finset.sum_apply, cellVector]
  rw [sum_range_ite_eq_card (fun i => min (W i ω).1.1 (W i ω).2 = j ∧ (W i ω).1.1 ≤ (W i ω).2 ∧
    (W i ω).1.2 = c)]
  simp only [empiricalCauseData, CompetingRiskData.ofSubjects]
  congr 2
  ext i
  by_cases h : (W i ω).1.1 ≤ (W i ω).2 <;> simp [h]

/-- The at-risk coordinates of the summed cell vectors are the at-risk counts. -/
theorem sum_cellVector_inr (W : ℕ → Ω → (Fin k × Fin r) × Fin k) (n : ℕ) (ω : Ω) (j : Fin k) :
    (∑ i ∈ range n, cellVector (W i ω)) (Sum.inr j) = (empiricalCauseData W n ω).atRisk j := by
  classical
  simp only [WithLp.ofLp_sum, Finset.sum_apply, cellVector]
  rw [sum_range_ite_eq_card (fun i => j ≤ min (W i ω).1.1 (W i ω).2),
    ← CompetingRiskData.atRisk_toCensoredData, toCensoredData_empiricalCauseData, empiricalData,
    CensoredData.atRisk_ofSubjects]

/-- On the summed cell vectors (the counts), the Aalen–Johansen map is the joint Kaplan–Meier and
Aalen–Johansen estimator of the grouped data. -/
theorem ajMap_sum_cellVector (m : Fin k) (W : ℕ → Ω → (Fin k × Fin r) × Fin k) (n : ℕ)
    (ω : Ω) :
    ajMap m (∑ i ∈ range n, cellVector (W i ω)) = estimator m (empiricalCauseData W n ω) := by
  set D := empiricalCauseData W n ω with hD
  have hfac : ∀ l, factor (∑ i ∈ range n, cellVector (W i ω)) l = D.toCensoredData.kmFactor l := by
    intro l
    simp only [factor, sum_cellVector_inl, sum_cellVector_inr, CensoredData.kmFactor,
      CompetingRiskData.toCensoredData_deaths, CompetingRiskData.totalEvents, Nat.cast_sum,
      CompetingRiskData.atRisk_toCensoredData, hD]
  funext a
  rcases a with ⟨_ | c, j⟩
  · simp only [ajMap, estimator, CensoredData.kmSurvival, CompetingRiskData.toCensoredData_time,
      hfac]
    exact prod_congr (by ext l; simp [D.strictMono_time.le_iff_le]) fun _ _ => rfl
  · simp only [ajMap, estimator, CompetingRiskData.cumulativeIncidence,
      CompetingRiskData.cifIncrement, CompetingRiskData.survivalBefore, hfac, sum_cellVector_inl,
      sum_cellVector_inr]
    exact sum_congr (by ext l; simp [D.strictMono_time.le_iff_le]) fun _ _ => rfl

/-- **The estimator is the Aalen–Johansen map of the empirical cell means**: the joint
Kaplan–Meier and Aalen–Johansen estimate of the first `n` subjects is `ajMap m` evaluated at the
empirical mean cell vector (for every `n`, including `n = 0`). -/
theorem ajMap_empiricalMean (m : Fin k) (W : ℕ → Ω → (Fin k × Fin r) × Fin k) (n : ℕ)
    (ω : Ω) : ajMap m (empiricalMean W n ω) = estimator m (empiricalCauseData W n ω) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 : empiricalMean W 0 ω = ∑ i ∈ range 0, cellVector (W i ω) := by simp [empiricalMean]
    rw [h0, ajMap_sum_cellVector]
  · rw [empiricalMean, ajMap_smul m (inv_ne_zero (Nat.cast_ne_zero.2 hn)), ajMap_sum_cellVector]

end Empirical

/-! ### The joint central limit theorem -/

section CLT

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure ((Fin k × Fin r) × Fin k)} {W : ℕ → Ω → (Fin k × Fin r) × Fin k}

private lemma memLp_cellVector {Y : Ω → (Fin k × Fin r) × Fin k} (hY : AEMeasurable Y P) :
    MemLp (fun ω => cellVector (Y ω)) 2 P :=
  (memLp_map_measure_iff (g := cellVector (k := k) (r := r))
    Measurable.of_discrete.aestronglyMeasurable hY).1 MemLp.of_discrete

/-- The at-risk mass is antitone in the grid index. -/
theorem causeAtRiskMass_antitone [IsFiniteMeasure μ] : Antitone (causeAtRiskMass μ) :=
  fun _ _ hij => measureReal_mono fun _ hz => le_trans hij hz

/-- A nonzero at-risk mass at the horizon `m` gives a nonzero at-risk mass at every `l ≤ m`. -/
theorem causeAtRiskMass_ne_zero_of_le [IsFiniteMeasure μ] {l m : Fin k} (hlm : l ≤ m)
    (hm : causeAtRiskMass μ m ≠ 0) : causeAtRiskMass μ l ≠ 0 :=
  (lt_of_lt_of_le (lt_of_le_of_ne measureReal_nonneg (Ne.symm hm))
    (causeAtRiskMass_antitone hlm)).ne'

/-- **The mean cell vector**: for a subject with law `μ`, the mean of the cell indicator vector is
`cellMean μ`, the vector of cause-specific event masses and at-risk masses. -/
theorem integral_cellVector {Y : Ω → (Fin k × Fin r) × Fin k} (hY : HasLaw Y μ P) :
    ∫ ω, cellVector (Y ω) ∂P = cellMean μ := by
  have hint := (memLp_cellVector hY.aemeasurable).integrable one_le_two
  have key : ∀ s : Set ((Fin k × Fin r) × Fin k),
      ∫ ω, s.indicator (1 : (Fin k × Fin r) × Fin k → ℝ) (Y ω) ∂P = μ.real s := fun s => by
    have h := hY.integral_comp (f := s.indicator (1 : (Fin k × Fin r) × Fin k → ℝ))
      Measurable.of_discrete.aestronglyMeasurable
    rw [Function.comp_def] at h
    rw [h, integral_indicator_one (Set.toFinite s).measurableSet]
  ext i
  have hproj : ∫ ω, cellVector (Y ω) i ∂P = (∫ ω, cellVector (Y ω) ∂P) i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hint
  rw [← hproj]
  rcases i with ⟨j, c⟩ | j
  · have h : ∀ w : (Fin k × Fin r) × Fin k, (cellVector w) (Sum.inl (j, c)) =
        {w : (Fin k × Fin r) × Fin k | min w.1.1 w.2 = j ∧ w.1.1 ≤ w.2 ∧ w.1.2 = c}.indicator 1 w :=
      fun w => by simp [cellVector, Set.indicator_apply]
    simp_rw [h]
    rw [key]
    rfl
  · have h : ∀ w : (Fin k × Fin r) × Fin k, (cellVector w) (Sum.inr j) =
        {w : (Fin k × Fin r) × Fin k | j ≤ min w.1.1 w.2}.indicator 1 w :=
      fun w => by simp [cellVector, Set.indicator_apply]
    simp_rw [h]
    rw [key]
    rfl

/-- The cell-count central limit theorem in the empirical-mean scaling: the centered empirical
mean cell vectors, scaled by `√n`, converge in distribution to a Gaussian vector with the
covariance of one subject's cell indicator vector. -/
theorem exists_tendstoInDistribution_empiricalMean (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) μ P) :
    ∃ A : EuclideanSpace ℝ (Cell k r) →L[ℝ] EuclideanSpace ℝ (Cell k r),
      HasGaussianLaw A (stdGaussian (EuclideanSpace ℝ (Cell k r))) ∧
      (∀ t : EuclideanSpace ℝ (Cell k r), HasLaw (fun z => ⟪A z, t⟫)
        (gaussianReal 0 (Var[fun ω => ⟪cellVector (W 0 ω), t⟫; P]).toNNReal)
        (stdGaussian (EuclideanSpace ℝ (Cell k r)))) ∧
      TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (empiricalMean W n ω - cellMean μ))
        atTop A (fun _ => P) (stdGaussian (EuclideanSpace ℝ (Cell k r))) := by
  have hX : MemLp (fun ω => cellVector (W 0 ω)) 2 P := memLp_cellVector (hlaw 0).aemeasurable
  have hindX : iIndepFun (fun i ω => cellVector (W i ω)) P :=
    hind.comp (fun _ => cellVector) fun _ => Measurable.of_discrete
  have hident : ∀ i, IdentDistrib (fun ω => cellVector (W i ω)) (fun ω => cellVector (W 0 ω))
      P P := fun i =>
    (⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩ :
      IdentDistrib (W i) (W 0) P P).comp (u := cellVector) Measurable.of_discrete
  obtain ⟨A, hAg, hA, hclt⟩ := exists_tendstoInDistribution_inv_sqrt_smul_sum_sub hX hindX hident
  refine ⟨A, hAg, hA, ?_⟩
  rw [integral_cellVector (hlaw 0)] at hclt
  refine hclt.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun _ => rfl)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [empiricalMean]
  · have hs : (√(n : ℝ)) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    have hpos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))
    simp only [empiricalMean, smul_sub, smul_smul, ← Nat.cast_smul_eq_nsmul ℝ]
    congr 2
    · field_simp
      rw [hs]
    · field_simp
      rw [hs]

/-- **Fixed-grid joint central limit theorem for Kaplan–Meier and Aalen–Johansen.** Let the
subjects `Wᵢ = ((Tᵢ, Jᵢ), Cᵢ)` be i.i.d. with law `μ` on `(Fin k × Fin r) × Fin k` (no
independence between `(T, J)` and `C` is assumed here), and let the observed at-risk mass at the
horizon be positive, `P(min T C ≥ m) ≠ 0`. Then the joint vector of the Kaplan–Meier survival
and all `r` Aalen–Johansen cumulative incidences at every grid index `j ≤ m`, centered at its
plug-in limit `ajMap m (cellMean μ)` and scaled by `√n`, converges in distribution to
`L (A z)`, where `L` is the derivative of the Aalen–Johansen map at the mean cell vector and
`A z` is the Gaussian limit of the cell-count central limit theorem
(`exists_tendstoInDistribution_empiricalMean`). The covariance of the limit is identified in
`hasLaw_sum_mul_fderiv_ajMap`. Grid times only: no process convergence in `D[0, τ]` is
claimed. -/
theorem exists_tendstoInDistribution_estimator (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) μ P) (m : Fin k) (hm : causeAtRiskMass μ m ≠ 0) :
    ∃ A : EuclideanSpace ℝ (Cell k r) →L[ℝ] EuclideanSpace ℝ (Cell k r),
      HasGaussianLaw A (stdGaussian (EuclideanSpace ℝ (Cell k r))) ∧
      (∀ t : EuclideanSpace ℝ (Cell k r), HasLaw (fun z => ⟪A z, t⟫)
        (gaussianReal 0 (Var[fun ω => ⟪cellVector (W 0 ω), t⟫; P]).toNNReal)
        (stdGaussian (EuclideanSpace ℝ (Cell k r)))) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) •
          (estimator m (empiricalCauseData W n ω) - ajMap m (cellMean μ)))
        atTop (fun z => fderiv ℝ (ajMap m) (cellMean μ) (A z)) (fun _ => P)
        (stdGaussian (EuclideanSpace ℝ (Cell k r))) := by
  have : IsProbabilityMeasure μ := (hlaw 0).isProbabilityMeasure_iff.1 inferInstance
  obtain ⟨A, hAg, hA, hclt⟩ := exists_tendstoInDistribution_empiricalMean hind hlaw
  refine ⟨A, hAg, hA, ?_⟩
  have hdiff : HasFDerivAt (ajMap m) (fderiv ℝ (ajMap m) (cellMean μ)) (cellMean μ) :=
    (differentiableAt_ajMap m fun l hl => causeAtRiskMass_ne_zero_of_le hl hm).hasFDerivAt
  have hmeas : ∀ n, AEMeasurable (empiricalMean W n) P := fun n => by
    change AEMeasurable (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ range n, cellVector (W i ω)) P
    exact (Finset.aemeasurable_fun_sum (range n) fun i _ =>
      (Measurable.of_discrete (f := cellVector (k := k) (r := r))).comp_aemeasurable
        (hlaw i).aemeasurable).const_smul ((n : ℝ)⁻¹)
  have hd := hclt.delta_method (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) hdiff
    hmeas    (fun n => (measurable_ajMap m).comp_aemeasurable (hmeas n))
  refine hd.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun _ => rfl)
  simp only [ajMap_empiricalMean]

end CLT

/-! ### The limit covariance -/

section Covariance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] {ν : Measure E}

/-- If every scalar projection `⟪A z, t⟫` has the centered Gaussian law with variance
`Var[⟪X, t⟫]`, then so does every continuous linear functional `φ (A z)`, with variance
`Var[φ X]` (Riesz representation of `φ`). -/
theorem hasLaw_clm_of_hasLaw_inner {A : E → E} {X : Ω → E}
    (hA : ∀ t : E, HasLaw (fun z => ⟪A z, t⟫) (gaussianReal 0 (Var[fun ω => ⟪X ω, t⟫; P]).toNNReal)
      ν) (φ : E →L[ℝ] ℝ) :
    HasLaw (fun z => φ (A z)) (gaussianReal 0 (Var[fun ω => φ (X ω); P]).toNNReal) ν := by
  have h : ∀ u, φ u = ⟪u, (InnerProductSpace.toDual ℝ E).symm φ⟫ := fun u => by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  simp_rw [h]
  exact hA _

end Covariance

section Limit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure ((Fin k × Fin r) × Fin k)} {W : ℕ → Ω → (Fin k × Fin r) × Fin k}

/-- The **influence vector** of one subject `w` at the horizon `m`: the derivative of the
Aalen–Johansen map at the mean cell vector `cellMean μ`, applied to the cell indicator vector of
`w`. Its covariance under the subject law is the covariance of the joint Gaussian limit
(`tendstoInDistribution_estimator`). -/
noncomputable def influence (μ : Measure ((Fin k × Fin r) × Fin k)) (m : Fin k)
    (w : (Fin k × Fin r) × Fin k) : Coord k r m → ℝ :=
  fderiv ℝ (ajMap m) (cellMean μ) (cellVector w)

/-- **Joint central limit theorem with its covariance.** Under the hypotheses of
`exists_tendstoInDistribution_estimator`, there is a Gaussian random vector `Y` (on the standard
Gaussian space of the cells) such that `√n · (estimator - ajMap m (cellMean μ)) → Y` in
distribution, and every linear combination `∑ₐ sₐ Yₐ` is centered Gaussian with variance
`Var[∑ₐ sₐ · influence μ m (W 0) a]`. Equivalently, the covariance matrix of `Y` is the covariance
matrix of the influence vector of one subject (`covariance_limit`). -/
theorem tendstoInDistribution_estimator (hind : iIndepFun W P) (hlaw : ∀ i, HasLaw (W i) μ P)
    (m : Fin k) (hm : causeAtRiskMass μ m ≠ 0) :
    ∃ Y : EuclideanSpace ℝ (Cell k r) → Coord k r m → ℝ,
      HasGaussianLaw Y (stdGaussian (EuclideanSpace ℝ (Cell k r))) ∧
      (∀ s : Coord k r m → ℝ, HasLaw (fun z => ∑ a, s a * Y z a)
        (gaussianReal 0 (Var[fun ω => ∑ a, s a * influence μ m (W 0 ω) a; P]).toNNReal)
        (stdGaussian (EuclideanSpace ℝ (Cell k r)))) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) •
          (estimator m (empiricalCauseData W n ω) - ajMap m (cellMean μ)))
        atTop Y (fun _ => P) (stdGaussian (EuclideanSpace ℝ (Cell k r))) := by
  obtain ⟨A, hAg, hA, hconv⟩ := exists_tendstoInDistribution_estimator hind hlaw m hm
  set L := fderiv ℝ (ajMap m) (cellMean μ)
  refine ⟨fun z => L (A z), hAg.map L, fun s => ?_, hconv⟩
  let φ : EuclideanSpace ℝ (Cell k r) →L[ℝ] ℝ :=
    ∑ a, s a • (ContinuousLinearMap.proj a).comp L
  have hφ : ∀ u, φ u = ∑ a, s a * L u a := fun u => by simp [φ]
  have h := hasLaw_clm_of_hasLaw_inner hA φ
  simp only [hφ] at h
  exact h

/-- **The full covariance matrix of the joint limit.** If `Y` is a limit vector as in
`tendstoInDistribution_estimator`, i.e. every linear combination `∑ₐ sₐ Yₐ` is centered Gaussian
with variance `Var[∑ₐ sₐ · influence μ m (W 0) a]`, then for all coordinates `a, b`,
`Cov(Yₐ, Y_b) = Cov(influenceₐ, influence_b)` under the subject law: the asymptotic covariance of
the joint Kaplan–Meier and Aalen–Johansen estimator is the covariance of the influence vector. -/
theorem covariance_limit (m : Fin k) {Y : EuclideanSpace ℝ (Cell k r) → Coord k r m → ℝ}
    (hY : ∀ s : Coord k r m → ℝ, HasLaw (fun z => ∑ a, s a * Y z a)
      (gaussianReal 0 (Var[fun ω => ∑ a, s a * influence μ m (W 0 ω) a; P]).toNNReal)
      (stdGaussian (EuclideanSpace ℝ (Cell k r))))
    (hW : AEMeasurable (W 0) P) (a b : Coord k r m) :
    cov[fun z => Y z a, fun z => Y z b; stdGaussian (EuclideanSpace ℝ (Cell k r))] =
      cov[fun ω => influence μ m (W 0 ω) a, fun ω => influence μ m (W 0 ω) b; P] := by
  classical
  set ν := stdGaussian (EuclideanSpace ℝ (Cell k r))
  set I : Coord k r m → Ω → ℝ := fun c ω => influence μ m (W 0 ω) c with hI
  set e : Coord k r m → Coord k r m → ℝ := fun c => Pi.single c 1 with he
  have hsingle : ∀ (c : Coord k r m) (f : Coord k r m → ℝ), ∑ d, e c d * f d = f c :=
    fun c f => by simp [he, Pi.single_apply]
  have hpair : ∀ (f : Coord k r m → ℝ), ∑ d, (e a + e b) d * f d = f a + f b := fun f => by
    simp only [Pi.add_apply, add_mul, sum_add_distrib, hsingle]
  -- Laws of the single coordinates and of the pair sum.
  have hYa : ∀ c, HasLaw (fun z => Y z c) (gaussianReal 0 (Var[I c; P]).toNNReal) ν := fun c => by
    have h := hY (e c)
    simp only [hsingle] at h
    exact h
  have hYab : HasLaw (fun z => Y z a + Y z b)
      (gaussianReal 0 (Var[fun ω => I a ω + I b ω; P]).toNNReal) ν := by
    have h := hY (e a + e b)
    simp only [hpair] at h
    exact h
  have hvar : ∀ {X : EuclideanSpace ℝ (Cell k r) → ℝ} {v : ℝ}, 0 ≤ v →
      HasLaw X (gaussianReal 0 v.toNNReal) ν → Var[X; ν] = v := fun hv hX => by
    rw [hX.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ hv]
  have hmemI : ∀ c, MemLp (I c) 2 P := fun c =>
    (memLp_map_measure_iff (g := fun w => influence μ m w c)
      Measurable.of_discrete.aestronglyMeasurable hW).1 MemLp.of_discrete
  have hmemY : ∀ c, MemLp (fun z => Y z c) 2 ν := fun c =>
    (hYa c).memLp_comp (p := 2) (f := id) (memLp_id_gaussianReal 2)
  have h1 := variance_add (hmemY a) (hmemY b)
  have h2 := variance_add (hmemI a) (hmemI b)
  rw [show ((fun z => Y z a) + fun z => Y z b) = fun z => Y z a + Y z b from rfl,
    hvar (variance_nonneg _ _) hYab, hvar (variance_nonneg _ _) (hYa a),
    hvar (variance_nonneg _ _) (hYa b)] at h1
  rw [show (I a + I b) = fun ω => I a ω + I b ω from rfl] at h2
  linarith

end Limit

/-! ### Identification under independent censoring -/

section Identification

/-- The estimand of the joint estimator: coordinate `(none, j)` is the survival `P(T > j)` of the
event time and coordinate `(some c, j)` is the cumulative incidence `F_c(j) = P(T ≤ j, J = c)`,
for a joint law `pTJ` of the event time and cause `(T, J)`. -/
noncomputable def target (pTJ : PMF (Fin k × Fin r)) (m : Fin k) : Coord k r m → ℝ
  | (none, j) => (PMF.map Prod.fst pTJ).toMeasure.real {t | j.1 < t}
  | (some c, j) => pTJ.toMeasure.real {x | x.1 ≤ j.1 ∧ x.2 = c}

/-- The marginal point mass of `T` is the sum over causes of the joint point masses. -/
theorem toReal_map_fst_apply (pTJ : PMF (Fin k × Fin r)) (l : Fin k) :
    ((PMF.map Prod.fst pTJ) l).toReal = ∑ c, (pTJ (l, c)).toReal := by
  classical
  rw [← ENNReal.toReal_sum fun _ _ => pTJ.apply_ne_top _, PMF.map_apply, tsum_fintype,
    Fintype.sum_prod_type]
  congr 1
  refine (sum_eq_single l (fun l' _ hl' => ?_) (by simp)).trans ?_
  · exact sum_eq_zero fun c _ => by simp [Ne.symm hl']
  · simp

/-- At-risk mass in the independent-censoring model: `P(min T C ≥ l) = P(T ≥ l) P(C ≥ l)`. -/
theorem causeAtRiskMass_indepCauseLaw_eq (pTJ : PMF (Fin k × Fin r)) (pC : PMF (Fin k))
    (l : Fin k) :
    causeAtRiskMass (indepCauseLaw pTJ pC) l =
      survivalMass (PMF.map Prod.fst pTJ) l * survivalMass pC l := by
  rw [causeAtRiskMass_indepCauseLaw, survivalMass_map_fst]

/-- **Identification**: in the independent-censoring model `indepCauseLaw pTJ pC`, with positive
at-risk mass at the horizon `m`, the Aalen–Johansen map at the mean cell vector is the estimand
`target pTJ m`: the survival `P(T > j)` and the cumulative incidences `P(T ≤ j, J = c)` for
`j ≤ m`. -/
theorem ajMap_cellMean_indepCauseLaw (pTJ : PMF (Fin k × Fin r)) (pC : PMF (Fin k)) (m : Fin k)
    (hm : causeAtRiskMass (indepCauseLaw pTJ pC) m ≠ 0) :
    ajMap m (cellMean (indepCauseLaw pTJ pC)) = target pTJ m := by
  have : IsProbabilityMeasure (indepCauseLaw pTJ pC) := by
    rw [indepCauseLaw]
    infer_instance
  set pT := PMF.map Prod.fst pTJ with hpT
  have hne : ∀ l ≤ m, survivalMass pT l ≠ 0 ∧ survivalMass pC l ≠ 0 := fun l hl => by
    have h := causeAtRiskMass_ne_zero_of_le hl hm
    rw [causeAtRiskMass_indepCauseLaw_eq] at h
    exact mul_ne_zero_iff.1 h
  have hfac : ∀ l ≤ m, factor (cellMean (indepCauseLaw pTJ pC)) l = 1 - hazard pT l := by
    intro l hl
    obtain ⟨hT, hC⟩ := hne l hl
    simp only [factor, cellMean, causeEventMass_indepCauseLaw, ← sum_mul,
      causeAtRiskMass_indepCauseLaw_eq, hazard, ← toReal_map_fst_apply]
    rw [mul_div_mul_right _ _ hC]
  have hinc : ∀ l ≤ m, ∀ c, (cellMean (indepCauseLaw pTJ pC)) (Sum.inl (l, c)) /
      (cellMean (indepCauseLaw pTJ pC)) (Sum.inr l) = (pTJ (l, c)).toReal / survivalMass pT l := by
    intro l hl c
    simp only [cellMean, causeEventMass_indepCauseLaw, causeAtRiskMass_indepCauseLaw_eq]
    rw [mul_div_mul_right _ _ (hne l hl).2]
  funext a
  rcases a with ⟨_ | c, j⟩
  · simp only [ajMap, target]
    rw [prod_congr rfl fun l hl => hfac l (le_trans (by simpa using hl) j.2),
      prod_one_sub_hazard pT j.1 (hne j.1 j.2).1]
  · simp only [ajMap, target]
    rw [measureReal_le_cause]
    refine sum_congr rfl fun l hl => ?_
    have hl : l ≤ m := le_trans (by simpa using hl) j.2
    rw [prod_congr rfl fun i hi => hfac i (le_trans (by simpa using hi : i < l).le hl),
      prod_lt_one_sub_hazard pT l (hne l hl).1, hinc l hl c]
    field_simp [(hne l hl).1]

end Identification

/-! ### The joint CLT under independent censoring, and the Kaplan–Meier marginal -/

section IndependentCensoring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℕ → Ω → (Fin k × Fin r) × Fin k}

/-- **Fixed-grid joint central limit theorem for the Aalen–Johansen and Kaplan–Meier estimators
under independent censoring.** Let the subjects `Wᵢ = ((Tᵢ, Jᵢ), Cᵢ)` be i.i.d. with law
`indepCauseLaw pTJ pC`, in which the event time and cause `(T, J)` are jointly independent of the
censoring time `C`, and let `P(min T C ≥ m) ≠ 0`. Then
`√n · (Ŝ(j) - P(T > j), F̂_c(j) - P(T ≤ j, J = c))_{c, j ≤ m}` converges in distribution to a
centered Gaussian vector `Y` whose covariance matrix is that of the influence vector of one
subject (`covariance_limit`). Grid times only; no process convergence in `D[0, τ]`. -/
theorem tendstoInDistribution_estimator_indepCauseLaw (pTJ : PMF (Fin k × Fin r))
    (pC : PMF (Fin k)) (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) (indepCauseLaw pTJ pC) P) (m : Fin k)
    (hm : causeAtRiskMass (indepCauseLaw pTJ pC) m ≠ 0) :
    ∃ Y : EuclideanSpace ℝ (Cell k r) → Coord k r m → ℝ,
      HasGaussianLaw Y (stdGaussian (EuclideanSpace ℝ (Cell k r))) ∧
      (∀ s : Coord k r m → ℝ, HasLaw (fun z => ∑ a, s a * Y z a)
        (gaussianReal 0
          (Var[fun ω => ∑ a, s a * influence (indepCauseLaw pTJ pC) m (W 0 ω) a; P]).toNNReal)
        (stdGaussian (EuclideanSpace ℝ (Cell k r)))) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) • (estimator m (empiricalCauseData W n ω) - target pTJ m))
        atTop Y (fun _ => P) (stdGaussian (EuclideanSpace ℝ (Cell k r))) := by
  rw [← ajMap_cellMean_indepCauseLaw pTJ pC m hm]
  exact tendstoInDistribution_estimator hind hlaw m hm

/-- **The Kaplan–Meier marginal**, as a corollary of the joint theorem: under independent
censoring with `P(min T C ≥ m) ≠ 0`, for every grid index `j ≤ m`,
`√n · (Ŝ(j) - P(T > j))` converges in distribution to a centered Gaussian whose variance is the
variance of the Kaplan–Meier coordinate of the influence vector of one subject. -/
theorem tendstoInDistribution_kmSurvival_indepCauseLaw (pTJ : PMF (Fin k × Fin r))
    (pC : PMF (Fin k)) (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) (indepCauseLaw pTJ pC) P) (m : Fin k)
    (hm : causeAtRiskMass (indepCauseLaw pTJ pC) m ≠ 0) (j : Fin k) (hj : j ≤ m) :
    ∃ Z : EuclideanSpace ℝ (Cell k r) → ℝ,
      HasLaw Z (gaussianReal 0
          (Var[fun ω => influence (indepCauseLaw pTJ pC) m (W 0 ω) (none, ⟨j, hj⟩); P]).toNNReal)
        (stdGaussian (EuclideanSpace ℝ (Cell k r))) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) * ((empiricalCauseData W n ω).toCensoredData.kmSurvival
          ((j : ℕ) : ℝ) - (PMF.map Prod.fst pTJ).toMeasure.real {t | j < t}))
        atTop Z (fun _ => P) (stdGaussian (EuclideanSpace ℝ (Cell k r))) := by
  classical
  obtain ⟨Y, -, hY, hconv⟩ := tendstoInDistribution_estimator_indepCauseLaw pTJ pC hind hlaw m hm
  set a : Coord k r m := (none, ⟨j, hj⟩)
  refine ⟨fun z => Y z a, ?_, ?_⟩
  · have h := hY (Pi.single a 1)
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true] at h
    exact h
  · refine (hconv.continuous_comp (continuous_apply a)).congr
      (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun _ => rfl)
    rfl

end IndependentCensoring

end MathlibExt.Probability.Statistics.AalenJohansenCLT
