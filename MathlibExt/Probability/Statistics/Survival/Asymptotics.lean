/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.Consistency
public import MathlibExt.Probability.Statistics.MultivariateCLT
public import MathlibExt.Probability.Statistics.DeltaMethod

/-!
# Asymptotic distribution of the Kaplan–Meier estimator on a finite grid

The setting is that of `SurvivalConsistency`: subjects `Zᵢ = (Tᵢ, Cᵢ)` are independent with a
common law `μ` on `Fin k × Fin k`, and one observes the follow-up index `min Tᵢ Cᵢ` and the event
flag `Tᵢ ≤ Cᵢ` (ties count as events). Each subject falls into exactly one of the `2k`
**cells** `(j, b) : Fin k × Bool` (`cell`), and the grouped data `empiricalData Z n ω` are
determined by the empirical cell proportions `p̂ₙ` (`cellProportions`), vectors in the Euclidean
space `CellSpace k = EuclideanSpace ℝ (Fin k × Bool)`.

## Main results

* `tendstoInDistribution_cellProportions`: **joint CLT for the cell proportions**:
  `√n • (p̂ₙ - p) →ᵈ Y` for any `Y` whose projections are centered Gaussians with the variances of
  the projections of the cell indicator `cellVec Z₀`; `exists_tendstoInDistribution_cellProportions`
  constructs such a Gaussian `Y`.
* `kmMap_cellProportions`: the Kaplan–Meier estimate at grid time `m` is `g(p̂ₙ)` for the explicit
  map `g = kmMap m`; `kmMap_cellProbs_indepLaw`: under independent censoring `g(p) = P(T > m)`.
* `hasFDerivAt_kmMap`: `g` is differentiable at `p` with the explicit derivative
  `L = kmMapDeriv m p` (product-rule form), provided `P(min T C ≥ j) ≠ 0` for `j ≤ m`;
  `kmMapDeriv_eq_logForm` gives the log-derivative form
  `L v = -g(p) ∑_{j ≤ m} (Yⱼ v(j, true) - eⱼ Aⱼ(v)) / (Yⱼ (Yⱼ - eⱼ))`.
* `tendstoInDistribution_kmSurvival`: **asymptotic distribution of Kaplan–Meier**: under
  independent censoring with `P(min T C ≥ m) ≠ 0`, `√n (Ŝₙ(m) - P(T > m)) →ᵈ L Y`
  (delta method); `exists_tendstoInDistribution_kmSurvival` is the same with the constructed `Y`.

## Proof

The cell indicators `cellVec Zᵢ` are i.i.d. bounded random vectors with mean `p` (`cellProbs`), so
the multivariate CLT applies; `√n • (p̂ₙ - p)` equals its normalized centered sum at every `n`
(`sqrt_smul_cellProportions_sub`), so no eventual-equality argument is needed. The delta method
then applies to `g`, a finite product of `1 - (linear) / (linear)` factors, and the identities
`g(p̂ₙ) = Ŝₙ(m)` (every `n`) and `g(p) = P(T > m)` (`prod_one_sub_hazard`) rewrite the result.

## Scope

Fixed grid time `m`, positive at-risk mass at `m`; no uniformity in `m`, no process-level
(Skorokhod) statement. The limit is `L Y` with `L` explicit; its variance is not identified here.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.SurvivalAsymptotics

open MeasureTheory ProbabilityTheory Filter Finset Topology RealInnerProductSpace
open MathlibExt.Probability.Statistics.Censoring MathlibExt.Probability.Statistics.KaplanMeier
open MathlibExt.Probability.Statistics.SurvivalConsistency

variable {k : ℕ}

/-! ### Cells of the observed data -/

/-- The observed cell of a subject with event and censoring times `z = (T, C)`: the follow-up
index `min T C` together with the event flag `T ≤ C` (ties count as events). -/
def cell (z : Fin k × Fin k) : Fin k × Bool := (min z.1 z.2, decide (z.1 ≤ z.2))

/-- The space of cell vectors, `ℝ^(Fin k × Bool)` with its Euclidean structure. -/
abbrev CellSpace (k : ℕ) := EuclideanSpace ℝ (Fin k × Bool)

/-- The indicator vector of the observed cell of a subject: the basis vector at `cell z`. -/
noncomputable def cellVec (z : Fin k × Fin k) : CellSpace k := EuclideanSpace.single (cell z) 1

/-- The observed **censoring mass** at grid point `j` under the joint law `μ` of `(T, C)`:
`P(min T C = j, ¬ T ≤ C)`. -/
noncomputable def obsCensMass (μ : Measure (Fin k × Fin k)) (j : Fin k) : ℝ :=
  μ.real {z | min z.1 z.2 = j ∧ ¬ z.1 ≤ z.2}

/-- The vector of cell probabilities of the law `μ` of `(T, C)`: the cell `(j, true)` has mass
`obsEventMass μ j` and the cell `(j, false)` has mass `obsCensMass μ j`. -/
noncomputable def cellProbs (μ : Measure (Fin k × Fin k)) : CellSpace k :=
  WithLp.toLp 2 fun c => μ.real (cell ⁻¹' {c})

/-- The empirical cell proportions of the first `n` subjects of the sequence `Z`. -/
noncomputable def cellProportions {Ω : Type*} (Z : ℕ → Ω → Fin k × Fin k) (n : ℕ) (ω : Ω) :
    CellSpace k :=
  (n : ℝ)⁻¹ • ∑ i ∈ range n, cellVec (Z i ω)

/-- The total mass of the cells at or after grid index `j`, as a linear functional. At the cell
probabilities it is the at-risk mass `P(min T C ≥ j)`; at the empirical proportions it is the
at-risk proportion `nⱼ / n`. -/
noncomputable def cellAtRisk (j : Fin k) : CellSpace k →L[ℝ] ℝ :=
  ∑ c with j ≤ c.1, EuclideanSpace.proj c

theorem cellAtRisk_apply (j : Fin k) (v : CellSpace k) :
    cellAtRisk j v = ∑ c with j ≤ c.1, v c := by
  simp [cellAtRisk]

theorem cellVec_apply (z : Fin k × Fin k) (c : Fin k × Bool) :
    cellVec z c = (cell ⁻¹' {c}).indicator 1 z := by
  by_cases h : cell z = c
  · simp [cellVec, h]
  · simp [cellVec, h]

theorem cellAtRisk_cellVec (j : Fin k) (z : Fin k × Fin k) :
    cellAtRisk j (cellVec z) = {z : Fin k × Fin k | j ≤ min z.1 z.2}.indicator 1 z := by
  rw [cellAtRisk_apply]
  by_cases h : j ≤ min z.1 z.2
  · rw [sum_eq_single (cell z),
      Set.indicator_of_mem (show z ∈ {z : Fin k × Fin k | j ≤ min z.1 z.2} from h)]
    · simp [cellVec]
    · intro c _ hc
      simp [cellVec, Ne.symm hc]
    · intro hz; simp [cell, h] at hz
  · rw [sum_eq_zero]
    · simp only [Set.indicator_of_notMem (show z ∉ {z : Fin k × Fin k | j ≤ min z.1 z.2} from h)]
    · intro c hc
      have hc' : cell z ≠ c := by
        rintro rfl; simp only [mem_filter, mem_univ, true_and, cell] at hc; exact h hc
      simp [cellVec, hc']

theorem cellProbs_apply (μ : Measure (Fin k × Fin k)) (c : Fin k × Bool) :
    cellProbs μ c = μ.real (cell ⁻¹' {c}) := rfl

theorem cellProbs_true (μ : Measure (Fin k × Fin k)) (j : Fin k) :
    cellProbs μ (j, true) = obsEventMass μ j := by
  rw [cellProbs_apply, obsEventMass]
  congr 1
  ext z
  simp [cell]

theorem cellProbs_false (μ : Measure (Fin k × Fin k)) (j : Fin k) :
    cellProbs μ (j, false) = obsCensMass μ j := by
  rw [cellProbs_apply, obsCensMass]
  congr 1
  ext z
  simp [cell]

theorem measurable_cellVec : Measurable (cellVec (k := k)) := measurable_of_finite _

/-- The mean of the cell indicator vector is the vector of cell probabilities. -/
theorem integral_cellVec (μ : Measure (Fin k × Fin k)) [IsFiniteMeasure μ] :
    ∫ z, cellVec z ∂μ = cellProbs μ := by
  ext c
  have h := (EuclideanSpace.proj (𝕜 := ℝ) c).integral_comp_comm
    (μ := μ) (φ := cellVec) (Integrable.of_finite)
  simp only [PiLp.proj_apply] at h
  rw [← h, cellProbs_apply]
  simp_rw [cellVec_apply]
  exact integral_indicator_one ((Set.toFinite _).measurableSet)

theorem cellAtRisk_cellProbs (μ : Measure (Fin k × Fin k)) [IsFiniteMeasure μ] (j : Fin k) :
    cellAtRisk j (cellProbs μ) = obsAtRiskMass μ j := by
  rw [← integral_cellVec, ← (cellAtRisk j).integral_comp_comm Integrable.of_finite]
  simp_rw [cellAtRisk_cellVec]
  exact integral_indicator_one ((Set.toFinite _).measurableSet)

/-! ### Deliverable 1: joint central limit theorem for the cell proportions -/

section CLT

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {μ : Measure (Fin k × Fin k)} {Z : ℕ → Ω → Fin k × Fin k}

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The scaled centered cell proportions are the scaled centered sums of the cell vectors, at
every `n` (both sides vanish at `n = 0`). -/
theorem sqrt_smul_cellProportions_sub (μ : Measure (Fin k × Fin k)) (n : ℕ) (ω : Ω) :
    √(n : ℝ) • (cellProportions Z n ω - cellProbs μ) =
      (√(n : ℝ))⁻¹ • (∑ i ∈ range n, cellVec (Z i ω) - n • cellProbs μ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [cellProportions, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_sub, smul_smul, smul_smul]
  congr 2 <;> field_simp <;> simp [Real.sq_sqrt hn'.le]

/-- **Joint central limit theorem for the cell proportions** (interface form). Let the subjects
`Zᵢ = (Tᵢ, Cᵢ)` be independent with common law `μ`. If `Y` is a random vector of cell space all
of whose projections `⟪Y, t⟫` are centered real Gaussians with the variance of `⟪cellVec Z₀, t⟫`,
then `√n • (p̂ₙ - p)` converges in distribution to `Y`, where `p̂ₙ` are the empirical cell
proportions and `p` the cell probabilities. No independence of `T` and `C` is assumed. -/
theorem tendstoInDistribution_cellProportions (hind : iIndepFun Z P)
    (hlaw : ∀ i, HasLaw (Z i) μ P) {Y : Ω' → CellSpace k} (hY : AEMeasurable Y P')
    (hYlaw : ∀ t : CellSpace k, HasLaw (fun ω ↦ ⟪Y ω, t⟫)
      (gaussianReal 0 (Var[fun z ↦ ⟪cellVec z, t⟫; μ]).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (cellProportions Z n ω - cellProbs μ))
      atTop Y (fun _ ↦ P) P' := by
  have : IsProbabilityMeasure μ := (hlaw 0).isProbabilityMeasure_iff.1 inferInstance
  set X : ℕ → Ω → CellSpace k := fun i ω ↦ cellVec (Z i ω) with hX
  have hXmeas : ∀ i, AEMeasurable (X i) P := fun i ↦
    measurable_cellVec.comp_aemeasurable (hlaw i).aemeasurable
  have hmean : ∫ ω, X 0 ω ∂P = cellProbs μ := by
    rw [← integral_cellVec μ]
    exact (hlaw 0).integral_comp measurable_cellVec.aestronglyMeasurable
  have hmem : MemLp (X 0) 2 P := by
    refine MemLp.of_bound (hXmeas 0).aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ ?_)
    simp [hX, cellVec]
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i ↦
    (⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩ :
      IdentDistrib (Z i) (Z 0) P P).comp measurable_cellVec
  have hvar : ∀ t : CellSpace k,
      Var[fun ω ↦ ⟪X 0 ω, t⟫; P] = Var[fun z ↦ ⟪cellVec z, t⟫; μ] := fun t ↦ by
    rw [← (hlaw 0).map_eq, variance_map (measurable_of_finite _).aemeasurable
      (hlaw 0).aemeasurable]
    rfl
  have h := tendstoInDistribution_inv_sqrt_smul_sum_sub hY (fun t ↦ by rw [hvar]; exact hYlaw t)
    hmem (hind.comp (fun _ ↦ cellVec) fun _ ↦ measurable_cellVec) hident
  rw [hmean] at h
  refine h.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
  exact (sqrt_smul_cellProportions_sub μ n ω).symm

/-- **Joint central limit theorem for the cell proportions**, with a constructed Gaussian limit
`A` on the standard Gaussian space of `CellSpace k`. -/
theorem exists_tendstoInDistribution_cellProportions (hind : iIndepFun Z P)
    (hlaw : ∀ i, HasLaw (Z i) μ P) :
    ∃ A : CellSpace k →L[ℝ] CellSpace k, HasGaussianLaw A (stdGaussian (CellSpace k)) ∧
      (∀ t : CellSpace k, HasLaw (fun z ↦ ⟪A z, t⟫)
        (gaussianReal 0 (Var[fun z ↦ ⟪cellVec z, t⟫; μ]).toNNReal)
        (stdGaussian (CellSpace k))) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (cellProportions Z n ω - cellProbs μ))
        atTop A (fun _ ↦ P) (stdGaussian (CellSpace k)) := by
  have : IsProbabilityMeasure μ := (hlaw 0).isProbabilityMeasure_iff.1 inferInstance
  have hmem : MemLp cellVec 2 μ :=
    MemLp.of_bound measurable_cellVec.aestronglyMeasurable 1 (ae_of_all _ fun z ↦ by
      simp [cellVec])
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal hmem
  exact ⟨A, IsGaussian.hasGaussianLaw_id.map A, hA,
    tendstoInDistribution_cellProportions hind hlaw A.continuous.aemeasurable hA⟩

end CLT

/-! ### Deliverable 2: the delta method for Kaplan–Meier at a grid time -/

section KaplanMeierMap

/-- The Kaplan–Meier map at grid index `m` on cell space:
`g(v) = ∏_{j ≤ m} (1 - v(j, true) / ∑_{l ≥ j} (v(l, true) + v(l, false)))`. At the empirical cell
proportions it is the Kaplan–Meier estimate (`kmMap_cellProportions`), and at the cell
probabilities of the independent censoring model it is `P(T > m)` (`kmMap_cellProbs_indepLaw`). -/
noncomputable def kmMap (m : Fin k) (v : CellSpace k) : ℝ :=
  ∏ j with j ≤ m, (1 - v (j, true) / cellAtRisk j v)

/-- The derivative of `kmMap m` at `p`, in product-rule form:
`L v = ∑_{j ≤ m} (∏_{l ≤ m, l ≠ j} (1 - eₗ / Yₗ)) · (eⱼ Aⱼ(v) - Yⱼ v(j, true)) / Yⱼ²`,
where `eⱼ = p(j, true)`, `Aⱼ = cellAtRisk j` and `Yⱼ = Aⱼ(p)`. See `kmMapDeriv_eq_logForm` for the
log-derivative form. -/
noncomputable def kmMapDeriv (m : Fin k) (p : CellSpace k) : CellSpace k →L[ℝ] ℝ :=
  ∑ j with j ≤ m, (∏ l ∈ ({l | l ≤ m} : Finset (Fin k)).erase j,
      (1 - p (l, true) / cellAtRisk l p)) •
    ((cellAtRisk j p ^ 2)⁻¹ •
      (p (j, true) • cellAtRisk j - cellAtRisk j p • EuclideanSpace.proj (j, true)))

theorem kmMapDeriv_apply (m : Fin k) (p v : CellSpace k) :
    kmMapDeriv m p v = ∑ j with j ≤ m, (∏ l ∈ ({l | l ≤ m} : Finset (Fin k)).erase j,
      (1 - p (l, true) / cellAtRisk l p)) *
      ((p (j, true) * cellAtRisk j v - cellAtRisk j p * v (j, true)) / cellAtRisk j p ^ 2) := by
  simp only [kmMapDeriv, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, FunLike.coe_sub, Pi.sub_apply, smul_eq_mul, PiLp.proj_apply]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- **Differentiability of the Kaplan–Meier map**: if the at-risk masses `Aⱼ(p)` are nonzero for
`j ≤ m`, then `kmMap m` has Fréchet derivative `kmMapDeriv m p` at `p`. -/
theorem hasFDerivAt_kmMap (m : Fin k) {p : CellSpace k}
    (hp : ∀ j ≤ m, cellAtRisk j p ≠ 0) : HasFDerivAt (kmMap m) (kmMapDeriv m p) p := by
  classical
  have hfac : ∀ j ∈ ({j | j ≤ m} : Finset (Fin k)),
      HasFDerivAt (fun v : CellSpace k => 1 - v (j, true) / cellAtRisk j v)
        ((cellAtRisk j p ^ 2)⁻¹ •
          (p (j, true) • cellAtRisk j - cellAtRisk j p • EuclideanSpace.proj (j, true))) p := by
    intro j hj
    have hb := hp j (by simpa using hj)
    have ha : HasFDerivAt (fun v : CellSpace k => v (j, true))
        (EuclideanSpace.proj (𝕜 := ℝ) (j, true)) p :=
      (EuclideanSpace.proj (𝕜 := ℝ) (j, true)).hasFDerivAt
    have hinv := (hasFDerivAt_inv hb).comp p (cellAtRisk j).hasFDerivAt
    have h := (ha.mul hinv).const_sub 1
    refine h.congr_fderiv ?_
    ext v
    simp
    field_simp
    ring
  exact HasFDerivAt.finsetProd hfac

/-- The derivative of the Kaplan–Meier map vanishes at its own base point: `L p = 0`. -/
theorem kmMapDeriv_self (m : Fin k) (p : CellSpace k) : kmMapDeriv m p p = 0 := by
  rw [kmMapDeriv_apply]
  refine sum_eq_zero fun j _ => ?_
  rw [mul_comm (p (j, true)), sub_self, zero_div, mul_zero]

/-- **Log-derivative form of `kmMapDeriv`**: if `Yⱼ ≠ 0` and `Yⱼ ≠ eⱼ` for every `j ≤ m`, then
`L v = -g(p) ∑_{j ≤ m} (Yⱼ v(j, true) - eⱼ Aⱼ(v)) / (Yⱼ (Yⱼ - eⱼ))`, with `g = kmMap m`. -/
theorem kmMapDeriv_eq_logForm (m : Fin k) {p : CellSpace k} (hp : ∀ j ≤ m, cellAtRisk j p ≠ 0)
    (hpe : ∀ j ≤ m, cellAtRisk j p ≠ p (j, true)) (v : CellSpace k) :
    kmMapDeriv m p v = -kmMap m p * ∑ j with j ≤ m,
      (cellAtRisk j p * v (j, true) - p (j, true) * cellAtRisk j v) /
        (cellAtRisk j p * (cellAtRisk j p - p (j, true))) := by
  rw [kmMapDeriv_apply, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := by simpa using hj
  have hY := hp j hjm
  have hYe : cellAtRisk j p - p (j, true) ≠ 0 := sub_ne_zero.2 (hpe j hjm)
  have hf : 1 - p (j, true) / cellAtRisk j p ≠ 0 := by
    rw [one_sub_div hY]; exact div_ne_zero hYe hY
  have hprod : ∏ l ∈ ({l | l ≤ m} : Finset (Fin k)).erase j,
      (1 - p (l, true) / cellAtRisk l p) = kmMap m p / (1 - p (j, true) / cellAtRisk j p) := by
    rw [eq_div_iff hf, mul_comm, kmMap]
    exact mul_prod_erase _ (fun l => 1 - p (l, true) / cellAtRisk l p) hj
  rw [hprod, one_sub_div hY]
  field_simp
  ring

/-! #### The Kaplan–Meier map at the empirical proportions and at the cell probabilities -/

section Identities

variable {Ω : Type*} {Z : ℕ → Ω → Fin k × Fin k}

open Classical in
private lemma sum_range_indicator_cellVec (s : Set (Fin k × Fin k)) (n : ℕ) (ω : Ω) :
    ∑ i ∈ range n, s.indicator (1 : Fin k × Fin k → ℝ) (Z i ω) =
      ((#{i : Fin n | Z i ω ∈ s} : ℕ) : ℝ) := by
  rw [natCast_card_filter]
  rw [Fin.sum_univ_eq_sum_range (fun i => if Z i ω ∈ s then (1 : ℝ) else 0) n]
  simp [Set.indicator_apply]

private lemma apply_cellProportions (φ : CellSpace k →L[ℝ] ℝ) (n : ℕ) (ω : Ω) :
    φ (cellProportions Z n ω) = (n : ℝ)⁻¹ * ∑ i ∈ range n, φ (cellVec (Z i ω)) := by
  rw [cellProportions, map_smul, map_sum, smul_eq_mul]

/-- **The Kaplan–Meier map recovers the Kaplan–Meier estimate**: at the empirical cell
proportions of the first `n` subjects, `kmMap m` is the Kaplan–Meier estimate of
`empiricalData Z n ω` at the grid time `m`. This holds for every `n`, including `n = 0`. -/
theorem kmMap_cellProportions (m : Fin k) (n : ℕ) (ω : Ω) :
    kmMap m (cellProportions Z n ω) = (empiricalData Z n ω).kmSurvival ((m : ℕ) : ℝ) := by
  classical
  rw [kmSurvival_empiricalData, kmMap]
  refine prod_congr rfl fun j _ => ?_
  have hd : cellProportions Z n ω (j, true) =
      (n : ℝ)⁻¹ * (empiricalData Z n ω).deaths j := by
    have h := apply_cellProportions (Z := Z) (EuclideanSpace.proj (j, true)) n ω
    simp only [PiLp.proj_apply, cellVec_apply] at h
    rw [h, sum_range_indicator_cellVec, empiricalData, CensoredData.ofSubjects_deaths]
    congr 3
    ext i
    simp [cell, Prod.ext_iff]
  have hr : cellAtRisk j (cellProportions Z n ω) =
      (n : ℝ)⁻¹ * (empiricalData Z n ω).atRisk j := by
    rw [apply_cellProportions]
    simp only [cellAtRisk_cellVec]
    rw [sum_range_indicator_cellVec, empiricalData, CensoredData.atRisk_ofSubjects]
    congr 3
    ext i
    simp
  rw [hd, hr, CensoredData.kmFactor]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [empiricalData, CensoredData.atRisk_ofSubjects]
  · rw [mul_div_mul_left _ _ (inv_ne_zero (Nat.cast_ne_zero.2 hn.ne'))]

/-- At the cell probabilities of the independent censoring model, the Kaplan–Meier map is the
product-limit `∏_{j ≤ m} (1 - h(j)) = P(T > m)`, provided `P(min T C ≥ m) ≠ 0`. -/
theorem kmMap_cellProbs_indepLaw (pT pC : PMF (Fin k)) (m : Fin k)
    (hm : obsAtRiskMass (indepLaw pT pC) m ≠ 0) :
    kmMap m (cellProbs (indepLaw pT pC)) = pT.toMeasure.real {t | m < t} := by
  rw [← prod_one_sub_hazard pT m ((obsAtRiskMass_indepLaw_ne_zero_iff pT pC m).1 hm).1, kmMap]
  refine prod_congr rfl fun j hj => ?_
  rw [cellProbs_true, cellAtRisk_cellProbs, obsEventMass_div_obsAtRiskMass pT pC j
    (obsAtRiskMass_ne_zero_of_le _ (by simpa using hj) hm)]

end Identities

theorem measurable_kmMap (m : Fin k) : Measurable (kmMap m) := by
  unfold kmMap
  fun_prop

end KaplanMeierMap

section DeltaMethod

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {Z : ℕ → Ω → Fin k × Fin k}

theorem cellAtRisk_cellProbs_ne_zero (μ : Measure (Fin k × Fin k)) [IsFiniteMeasure μ]
    {m : Fin k} (hm : obsAtRiskMass μ m ≠ 0) :
    ∀ j ≤ m, cellAtRisk j (cellProbs μ) ≠ 0 := fun j hj => by
  rw [cellAtRisk_cellProbs]
  exact obsAtRiskMass_ne_zero_of_le μ hj hm

/-- **Asymptotic distribution of the Kaplan–Meier estimator at a grid time** (interface form).
Let the subjects `Zᵢ = (Tᵢ, Cᵢ)` be independent with the independent censoring law
`indepLaw pT pC`, and let `P(min T C ≥ m) ≠ 0`. If `Y` is a Gaussian limit for the cell
proportions as in `tendstoInDistribution_cellProportions`, then
`√n (Ŝₙ(m) - P(T > m)) →ᵈ L Y`, where `Ŝₙ` is the Kaplan–Meier estimate of the first `n` subjects
and `L = kmMapDeriv m p` is the derivative of the Kaplan–Meier map at the cell probabilities
`p`. -/
theorem tendstoInDistribution_kmSurvival (pT pC : PMF (Fin k)) (hind : iIndepFun Z P)
    (hlaw : ∀ i, HasLaw (Z i) (indepLaw pT pC) P) (m : Fin k)
    (hm : obsAtRiskMass (indepLaw pT pC) m ≠ 0) {Y : Ω' → CellSpace k} (hY : AEMeasurable Y P')
    (hYlaw : ∀ t : CellSpace k, HasLaw (fun ω ↦ ⟪Y ω, t⟫)
      (gaussianReal 0 (Var[fun z ↦ ⟪cellVec z, t⟫; indepLaw pT pC]).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) •
        ((empiricalData Z n ω).kmSurvival ((m : ℕ) : ℝ) - pT.toMeasure.real {t | m < t}))
      atTop (fun ω ↦ kmMapDeriv m (cellProbs (indepLaw pT pC)) (Y ω)) (fun _ ↦ P) P' := by
  have hX : ∀ n, AEMeasurable (cellProportions Z n) P := fun n ↦
    ((Finset.aemeasurable_fun_sum (range n) fun i _ ↦
      measurable_cellVec.comp_aemeasurable (hlaw i).aemeasurable).const_smul
        ((n : ℝ)⁻¹)).congr (ae_of_all _ fun ω ↦ by simp [cellProportions])
  have h := (tendstoInDistribution_cellProportions hind hlaw hY hYlaw).delta_method
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    (hasFDerivAt_kmMap m (cellAtRisk_cellProbs_ne_zero _ hm)) hX
    (fun n ↦ (measurable_kmMap m).comp_aemeasurable (hX n))
  refine h.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
  rw [kmMap_cellProportions, kmMap_cellProbs_indepLaw pT pC m hm]

/-- **Asymptotic distribution of the Kaplan–Meier estimator at a grid time**, with the
constructed Gaussian limit `A` of `exists_tendstoInDistribution_cellProportions`:
`√n (Ŝₙ(m) - P(T > m)) →ᵈ L ∘ A` on the standard Gaussian space of `CellSpace k`. -/
theorem exists_tendstoInDistribution_kmSurvival (pT pC : PMF (Fin k)) (hind : iIndepFun Z P)
    (hlaw : ∀ i, HasLaw (Z i) (indepLaw pT pC) P) (m : Fin k)
    (hm : obsAtRiskMass (indepLaw pT pC) m ≠ 0) :
    ∃ A : CellSpace k →L[ℝ] CellSpace k, HasGaussianLaw A (stdGaussian (CellSpace k)) ∧
      (∀ t : CellSpace k, HasLaw (fun z ↦ ⟪A z, t⟫)
        (gaussianReal 0 (Var[fun z ↦ ⟪cellVec z, t⟫; indepLaw pT pC]).toNNReal)
        (stdGaussian (CellSpace k))) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω ↦ √(n : ℝ) •
          ((empiricalData Z n ω).kmSurvival ((m : ℕ) : ℝ) - pT.toMeasure.real {t | m < t}))
        atTop (fun z ↦ kmMapDeriv m (cellProbs (indepLaw pT pC)) (A z)) (fun _ ↦ P)
        (stdGaussian (CellSpace k)) := by
  obtain ⟨A, hAG, hA, -⟩ := exists_tendstoInDistribution_cellProportions hind hlaw
  exact ⟨A, hAG, hA, tendstoInDistribution_kmSurvival pT pC hind hlaw m hm
    A.continuous.aemeasurable hA⟩

end DeltaMethod

/-! ### Deliverable 3: variance identification -/

section Variance

/-- The **population Greenwood sum** at grid index `m` of the cell-probability vector `p`:
`τ² = ∑_{j ≤ m} eⱼ / (Yⱼ (Yⱼ - eⱼ))`, with `eⱼ = p(j, true)` and `Yⱼ = cellAtRisk j p`. At the cell
probabilities of a law `μ` it is `∑_{j ≤ m} P(X = j, δ = 1) / (P(X ≥ j) P(X ≥ j, ¬(X = j, δ = 1)))`
(`greenwoodSum_cellProbs`), the limit of Greenwood's sum. -/
noncomputable def greenwoodSum (m : Fin k) (p : CellSpace k) : ℝ :=
  ∑ j with j ≤ m, p (j, true) / (cellAtRisk j p * (cellAtRisk j p - p (j, true)))

theorem greenwoodSum_cellProbs (μ : Measure (Fin k × Fin k)) [IsFiniteMeasure μ] (m : Fin k) :
    greenwoodSum m (cellProbs μ) = ∑ j with j ≤ m,
      obsEventMass μ j / (obsAtRiskMass μ j * (obsAtRiskMass μ j - obsEventMass μ j)) := by
  simp only [greenwoodSum, cellProbs_true, cellAtRisk_cellProbs]

/-- The `j`-th summand of the log-derivative form, as a function of a vector `v`. -/
private noncomputable def logTerm (p : CellSpace k) (j : Fin k) (v : CellSpace k) : ℝ :=
  (cellAtRisk j p * v (j, true) - p (j, true) * cellAtRisk j v) /
    (cellAtRisk j p * (cellAtRisk j p - p (j, true)))

private lemma single_apply_true (c : Fin k × Bool) (j : Fin k) :
    EuclideanSpace.single c (1 : ℝ) (j, true) = if c = (j, true) then 1 else 0 := by
  by_cases h : c = (j, true)
  · simp [h]
  · simp [h]

private lemma cellAtRisk_single (j : Fin k) (c : Fin k × Bool) :
    cellAtRisk j (EuclideanSpace.single c (1 : ℝ)) = if j ≤ c.1 then 1 else 0 := by
  rw [cellAtRisk_apply]
  by_cases h : j ≤ c.1
  · rw [sum_eq_single c (fun c' _ hc' => by simp [Ne.symm hc']) (fun hc => by simp [h] at hc)]
    simp [h]
  · simp only [h, ite_false]
    refine sum_eq_zero fun c' hc' => ?_
    have : c ≠ c' := by rintro rfl; simp [h] at hc'
    simp [this]

/-- The weighted Gram matrix of the log-derivative summands at the basis vectors is diagonal:
`∑_c p_c ξᵢ(e_c) ξⱼ(e_c) = [i = j] eⱼ / (Yⱼ (Yⱼ - eⱼ))`. -/
private lemma sum_logTerm_mul_logTerm (p : CellSpace k) {i j : Fin k}
    (hi : cellAtRisk i p ≠ 0) (hj : cellAtRisk j p ≠ 0) (hie : cellAtRisk i p ≠ p (i, true))
    (hje : cellAtRisk j p ≠ p (j, true)) :
    ∑ c, p c * (logTerm p i (EuclideanSpace.single c 1) * logTerm p j (EuclideanSpace.single c 1))
      = if i = j then p (j, true) / (cellAtRisk j p * (cellAtRisk j p - p (j, true))) else 0 := by
  set Yi := cellAtRisk i p with hYi
  set Yj := cellAtRisk j p with hYj
  set ei := p (i, true) with hei
  set ej := p (j, true) with hej
  have hDi : Yi * (Yi - ei) ≠ 0 := mul_ne_zero hi (sub_ne_zero.2 hie)
  have hDj : Yj * (Yj - ej) ≠ 0 := mul_ne_zero hj (sub_ne_zero.2 hje)
  have key : ∀ c : Fin k × Bool, p c * (logTerm p i (EuclideanSpace.single c 1) *
      logTerm p j (EuclideanSpace.single c 1)) =
      (Yi * Yj * (p c * ((if c = (i, true) then 1 else 0) * (if c = (j, true) then 1 else 0))) -
        Yi * ej * (p c * ((if c = (i, true) then 1 else 0) * (if j ≤ c.1 then 1 else 0))) -
        ei * Yj * (p c * ((if c = (j, true) then 1 else 0) * (if i ≤ c.1 then 1 else 0))) +
        ei * ej * (p c * ((if i ≤ c.1 then 1 else 0) * (if j ≤ c.1 then 1 else 0)))) /
        ((Yi * (Yi - ei)) * (Yj * (Yj - ej))) := by
    intro c
    simp only [logTerm, single_apply_true, cellAtRisk_single, ← hYi, ← hYj, ← hei, ← hej]
    field_simp
    ring
  have haa : ∑ c : Fin k × Bool, p c *
      ((if c = (i, true) then (1 : ℝ) else 0) * (if c = (j, true) then 1 else 0)) =
      if i = j then ej else 0 := by
    simp only [← ite_and, mul_ite, mul_one, mul_zero]
    by_cases h : i = j
    · subst h; simp [ej]
    · simp only [h, ite_false]
      refine sum_eq_zero fun c _ => ?_
      split_ifs with hc
      · exfalso
        simp only [Prod.ext_iff] at hc
        obtain ⟨⟨h1, -⟩, h2, -⟩ := hc
        exact h (h2.symm.trans h1)
      · rfl
  have har : ∀ a b : Fin k, ∑ c : Fin k × Bool, p c *
      ((if c = (a, true) then (1 : ℝ) else 0) * (if b ≤ c.1 then 1 else 0)) =
      if b ≤ a then p (a, true) else 0 := by
    intro a b
    simp only [← ite_and, mul_ite, mul_one, mul_zero]
    rw [sum_ite, sum_const_zero, add_zero]
    by_cases h : b ≤ a
    · simp only [h, ite_true]
      rw [sum_eq_single (a, true)]
      · intro c hc hne
        simp only [mem_filter, mem_univ, true_and] at hc
        exact absurd (by tauto) hne
      · intro hn; simp [h] at hn
    · simp only [h, ite_false]
      refine sum_eq_zero fun c hc => ?_
      simp only [mem_filter, mem_univ, true_and] at hc
      obtain ⟨h1, h2⟩ := hc
      exfalso
      subst h2
      exact h h1
  have hrr : ∑ c : Fin k × Bool, p c *
      ((if i ≤ c.1 then (1 : ℝ) else 0) * (if j ≤ c.1 then 1 else 0)) = cellAtRisk (max i j) p := by
    simp only [← ite_and, mul_ite, mul_one, mul_zero, cellAtRisk_apply, ← max_le_iff]
    rw [sum_ite, sum_const_zero, add_zero, max_comm]
  rw [sum_congr rfl fun c _ => key c, ← sum_div, sum_add_distrib, sum_sub_distrib,
    sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum, haa, har, har, hrr]
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [h.ne, not_le.2 h, h.le, max_eq_right h.le, ite_false, ite_true]
    field_simp
    ring
  · simp only [ite_true, le_refl, max_self]
    field_simp
    ring
  · simp only [h.ne', not_le.2 h, h.le, max_eq_left h.le, ite_false, ite_true]
    field_simp
    ring

/-- **The variance algebra**: for a vector `p` with `Yⱼ ≠ 0` for `j ≤ m` and `g(p) ≠ 0`, the
`p`-weighted sum of squares of the derivative at the basis vectors is `g(p)² τ²`:
`∑_c p_c (L e_c)² = kmMap m p ^ 2 * greenwoodSum m p`. No positivity or normalization of `p` is
needed. -/
theorem sum_mul_kmMapDeriv_single_sq (m : Fin k) {p : CellSpace k}
    (hp : ∀ j ≤ m, cellAtRisk j p ≠ 0) (hS : kmMap m p ≠ 0) :
    ∑ c, p c * kmMapDeriv m p (EuclideanSpace.single c 1) ^ 2 =
      kmMap m p ^ 2 * greenwoodSum m p := by
  have hpe : ∀ j ≤ m, cellAtRisk j p ≠ p (j, true) := by
    intro j hj he
    refine hS (prod_eq_zero (i := j) (by simpa using hj) ?_)
    rw [he, div_self (he ▸ hp j hj), sub_self]
  have hL : ∀ c : Fin k × Bool, kmMapDeriv m p (EuclideanSpace.single c 1) =
      -kmMap m p * ∑ j with j ≤ m, logTerm p j (EuclideanSpace.single c 1) := fun c =>
    kmMapDeriv_eq_logForm m hp hpe _
  have h1 : ∀ c : Fin k × Bool,
      p c * (-kmMap m p * ∑ j with j ≤ m, logTerm p j (EuclideanSpace.single c 1)) ^ 2 =
      kmMap m p ^ 2 * ∑ a with a ≤ m, ∑ b with b ≤ m, p c *
        (logTerm p a (EuclideanSpace.single c 1) * logTerm p b (EuclideanSpace.single c 1)) := by
    intro c
    rw [show p c * (-kmMap m p * ∑ j with j ≤ m, logTerm p j (EuclideanSpace.single c 1)) ^ 2 =
      kmMap m p ^ 2 * (p c * ((∑ j with j ≤ m, logTerm p j (EuclideanSpace.single c 1)) *
        ∑ j with j ≤ m, logTerm p j (EuclideanSpace.single c 1))) by ring, sum_mul_sum, mul_sum]
    simp_rw [mul_sum]
  simp_rw [hL, h1]
  rw [← mul_sum]
  rw [greenwoodSum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun a ha => ?_
  have ha' : a ≤ m := by simpa using ha
  rw [sum_comm, sum_congr rfl fun b hb => sum_logTerm_mul_logTerm p (hp a ha')
    (hp b (by simpa using hb)) (hpe a ha') (hpe b (by simpa using hb)), sum_ite_eq]
  simp only [ha, ite_true]

/-- The variance of a linear functional of the cell indicator:
`Var[φ(cellVec Z)] = ∑_c p_c φ(e_c)² - φ(p)²`, with `p = cellProbs μ`. -/
theorem variance_apply_cellVec (φ : CellSpace k →L[ℝ] ℝ) (μ : Measure (Fin k × Fin k))
    [IsProbabilityMeasure μ] :
    Var[fun z => φ (cellVec z); μ] =
      ∑ c, cellProbs μ c * φ (EuclideanSpace.single c 1) ^ 2 - φ (cellProbs μ) ^ 2 := by
  rw [variance_eq_sub MemLp.of_discrete]
  have h1 : ∫ z, φ (cellVec z) ∂μ = φ (cellProbs μ) := by
    rw [φ.integral_comp_comm Integrable.of_finite, integral_cellVec]
  let ψ : CellSpace k →L[ℝ] ℝ := ∑ c, φ (EuclideanSpace.single c 1) ^ 2 • EuclideanSpace.proj c
  have hψ : ∀ v : CellSpace k, ψ v = ∑ c, φ (EuclideanSpace.single c 1) ^ 2 * v c := fun v => by
    simp [ψ]
  have hψz : ∀ z, ψ (cellVec z) = (φ (cellVec z)) ^ 2 := fun z => by
    rw [hψ, sum_eq_single (cell z)]
    · simp [cellVec]
    · intro c _ hc; simp [cellVec, Ne.symm hc]
    · intro h; exact absurd (mem_univ _) h
  have h2 : ∫ z, ((fun z => φ (cellVec z)) ^ 2) z ∂μ = ∑ c, cellProbs μ c *
      φ (EuclideanSpace.single c 1) ^ 2 := by
    simp only [Pi.pow_apply, ← hψz]
    rw [ψ.integral_comp_comm Integrable.of_finite, integral_cellVec, hψ]
    exact sum_congr rfl fun _ _ => mul_comm _ _
  rw [h2, h1]

/-- **Variance identification**: if `P(min T C ≥ j) ≠ 0` for `j ≤ m` and `g(p) ≠ 0`, the
variance of the derivative `L = kmMapDeriv m p` applied to the cell indicator is
`g(p)² τ²` with `τ² = greenwoodSum m p`, where `p = cellProbs μ`. -/
theorem variance_kmMapDeriv_cellVec (μ : Measure (Fin k × Fin k)) [IsProbabilityMeasure μ]
    (m : Fin k) (hm : obsAtRiskMass μ m ≠ 0) (hS : kmMap m (cellProbs μ) ≠ 0) :
    Var[fun z => kmMapDeriv m (cellProbs μ) (cellVec z); μ] =
      kmMap m (cellProbs μ) ^ 2 * greenwoodSum m (cellProbs μ) := by
  rw [variance_apply_cellVec, kmMapDeriv_self, sq (0 : ℝ), mul_zero, sub_zero,
    sum_mul_kmMapDeriv_single_sq m (cellAtRisk_cellProbs_ne_zero μ hm) hS]

/-- A linear functional of a limit `Y` as in `tendstoInDistribution_cellProportions` is a centered
real Gaussian with the variance of the functional applied to the cell indicator. -/
theorem hasLaw_apply_of_hasLaw_inner {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {μ : Measure (Fin k × Fin k)} {Y : Ω' → CellSpace k}
    (hYlaw : ∀ t : CellSpace k, HasLaw (fun ω ↦ ⟪Y ω, t⟫)
      (gaussianReal 0 (Var[fun z ↦ ⟪cellVec z, t⟫; μ]).toNNReal) P')
    (φ : CellSpace k →L[ℝ] ℝ) :
    HasLaw (fun ω ↦ φ (Y ω)) (gaussianReal 0 (Var[fun z ↦ φ (cellVec z); μ]).toNNReal) P' := by
  have h : ∀ v : CellSpace k, ⟪v, (InnerProductSpace.toDual ℝ (CellSpace k)).symm φ⟫ = φ v :=
    fun v => by rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have := hYlaw ((InnerProductSpace.toDual ℝ (CellSpace k)).symm φ)
  simp only [h] at this
  exact this

/-- **The limit law of the Kaplan–Meier estimator**: under the hypotheses of
`tendstoInDistribution_kmSurvival` and `P(T > m) ≠ 0`, the limit `L Y` is the centered real
Gaussian with variance `S² τ²`, `S = P(T > m)` and `τ² = greenwoodSum m p` the population
Greenwood sum (`greenwoodSum_cellProbs`). -/
theorem hasLaw_kmMapDeriv_limit (pT pC : PMF (Fin k)) (m : Fin k)
    (hm : obsAtRiskMass (indepLaw pT pC) m ≠ 0) (hS : pT.toMeasure.real {t | m < t} ≠ 0)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {Y : Ω' → CellSpace k}
    (hYlaw : ∀ t : CellSpace k, HasLaw (fun ω ↦ ⟪Y ω, t⟫)
      (gaussianReal 0 (Var[fun z ↦ ⟪cellVec z, t⟫; indepLaw pT pC]).toNNReal) P') :
    HasLaw (fun ω ↦ kmMapDeriv m (cellProbs (indepLaw pT pC)) (Y ω))
      (gaussianReal 0 (pT.toMeasure.real {t | m < t} ^ 2 *
        greenwoodSum m (cellProbs (indepLaw pT pC))).toNNReal) P' := by
  have h := hasLaw_apply_of_hasLaw_inner hYlaw (kmMapDeriv m (cellProbs (indepLaw pT pC)))
  rwa [variance_kmMapDeriv_cellVec _ m hm (by rwa [kmMap_cellProbs_indepLaw pT pC m hm]),
    kmMap_cellProbs_indepLaw pT pC m hm] at h

end Variance

end MathlibExt.Probability.Statistics.SurvivalAsymptotics
