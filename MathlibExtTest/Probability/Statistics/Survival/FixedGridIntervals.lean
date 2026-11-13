/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.FixedGridIntervals
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter Topology
open MathlibExt.Probability.Statistics.Censoring
open MathlibExt.Probability.Statistics.CompetingRisks
open MathlibExt.Probability.Statistics.SurvivalConsistency
open MathlibExt.Probability.Statistics.AalenJohansenCLT
open MathlibExt.Probability.Statistics.ProcessInference
open MathlibExt.Probability.Statistics.FixedGridIntervals

namespace MathlibExtTest.Probability.Statistics.FixedGridIntervals

/-! ### Interval width and nominal level, from the definitions -/

/-- Concrete width: asymptotic variance `σ² = 1/4`, sample size `n = 16`, critical value `z = 2`.
The Wald interval `est ± z · σ / √n` is `[est - 1/4, est + 1/4]`, of width `1/2`. -/
example (est : ℝ) :
    waldInterval est (√(1 / 4 : ℝ) / √((16 : ℕ) : ℝ)) 2 = Set.Icc (est - 1 / 4) (est + 1 / 4) := by
  have h1 : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h2 : √((16 : ℕ) : ℝ) = 4 := by
    rw [show ((16 : ℕ) : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [waldInterval_div_sqrt_eq, h1, h2]
  norm_num

/-- The width of that interval: `2 · z · σ / √n = 1/2`. -/
example (est : ℝ) :
    (est + 2 * (√(1 / 4 : ℝ) / √((16 : ℕ) : ℝ))) - (est - 2 * (√(1 / 4 : ℝ) / √((16 : ℕ) : ℝ)))
      = 1 / 2 := by
  have h1 : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h2 : √((16 : ℕ) : ℝ) = 4 := by
    rw [show ((16 : ℕ) : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h1, h2]
  norm_num

/-- The nominal level at `z = 0` is `0`: `[-0, 0]` is a point and the standard normal has no
atoms. -/
theorem nominalLevel_zero : nominalLevel 0 = 0 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  rw [nominalLevel, neg_zero, Set.Icc_self, Measure.real, measure_singleton, ENNReal.toReal_zero]

/-- The nominal level is a probability. -/
example (z : ℝ) : 0 ≤ nominalLevel z ∧ nominalLevel z ≤ 1 :=
  ⟨nominalLevel_nonneg z, nominalLevel_le_one z⟩

/-! ### A concrete fixed grid with a concrete variance -/

section Concrete

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℕ → Ω → (Fin 3 × Fin 2) × Fin 3}

/-- Grid `Fin 3`, two causes, horizon `m = 1`. If the Kaplan–Meier coordinate at grid index `1`
has asymptotic variance `1/4`, the known-variance interval `Ŝ(1) ± 2 · (1/2) / √n` has coverage
tending to `nominalLevel 2`, and at `n = 16` it is `[Ŝ(1) - 1/4, Ŝ(1) + 1/4]`. -/
example (μ : Measure ((Fin 3 × Fin 2) × Fin 3)) (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) μ P) (hm : causeAtRiskMass μ 1 ≠ 0)
    (hv : asymVar μ 1 (none, ⟨1, le_rfl⟩) = 1 / 4) :
    Tendsto (fun n : ℕ => P.real {ω | ajMap 1 (cellMean μ) (none, ⟨1, le_rfl⟩) ∈
        waldInterval (estimator 1 (empiricalCauseData W n ω) (none, ⟨1, le_rfl⟩))
          (√(1 / 4 : ℝ) / √(n : ℝ)) 2})
      atTop (𝓝 (nominalLevel 2)) ∧
    ∀ ω, waldInterval (estimator 1 (empiricalCauseData W 16 ω) (none, ⟨1, le_rfl⟩))
        (√(1 / 4 : ℝ) / √((16 : ℕ) : ℝ)) 2 =
      Set.Icc (estimator 1 (empiricalCauseData W 16 ω) (none, ⟨1, le_rfl⟩) - 1 / 4)
        (estimator 1 (empiricalCauseData W 16 ω) (none, ⟨1, le_rfl⟩) + 1 / 4) := by
  refine ⟨?_, fun ω => ?_⟩
  · have h := tendsto_coverage_waldInterval_estimator_oracle hind hlaw 1 hm
      (none, ⟨1, le_rfl⟩) (by rw [hv]; norm_num) 2
    rwa [hv] at h
  · have h1 : √(1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h2 : √((16 : ℕ) : ℝ) = 4 := by
      rw [show ((16 : ℕ) : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [waldInterval_div_sqrt_eq, h1, h2]
    norm_num

/-- The fixed grid `g` of two coordinates: the survival at grid index `0` and the cumulative
incidence of cause `1` at grid index `1`. -/
def grid : Fin 2 → Coord 3 2 (1 : Fin 3)
  | 0 => (none, ⟨0, by decide⟩)
  | 1 => (some 1, ⟨1, le_rfl⟩)

/-- On the two-point grid, under independent censoring and nondegeneracy, the simultaneous band
covers `(P(T > 0), P(T ≤ 1, J = 1))` with limit probability at least `1 - 2 (1 - nominalLevel z)`
and at most `nominalLevel z`. -/
example (pTJ : PMF (Fin 3 × Fin 2)) (pC : PMF (Fin 3)) (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) (indepCauseLaw pTJ pC) P)
    (hm : causeAtRiskMass (indepCauseLaw pTJ pC) 1 ≠ 0)
    (hv : ∀ i, 0 < asymVar (indepCauseLaw pTJ pC) 1 (grid i)) (z : ℝ) :
    ∃ Y : EuclideanSpace ℝ (Cell 3 2) → Fin 2 → ℝ,
      1 - 2 * (1 - nominalLevel z) ≤ (stdGaussian (EuclideanSpace ℝ (Cell 3 2))).real
          {x | ∀ i, |Y x i| ≤ z * √(asymVar (indepCauseLaw pTJ pC) 1 (grid i))} ∧
        (stdGaussian (EuclideanSpace ℝ (Cell 3 2))).real
          {x | ∀ i, |Y x i| ≤ z * √(asymVar (indepCauseLaw pTJ pC) 1 (grid i))} ≤
          nominalLevel z := by
  obtain ⟨Y, -, -, -, hle, hbonf⟩ :=
    tendsto_coverage_gridBand_indepCauseLaw pTJ pC hind hlaw 1 hm grid hv
  refine ⟨Y, ?_, hle z ⟨0⟩⟩
  have h := hbonf z
  simpa using h

/-- The grid coordinates are the survival `P(T > 0)` and the cumulative incidence
`P(T ≤ 1, J = 1)`. -/
example (pTJ : PMF (Fin 3 × Fin 2)) :
    target pTJ 1 (grid 0) = (PMF.map Prod.fst pTJ).toMeasure.real {t | 0 < t} ∧
      target pTJ 1 (grid 1) = pTJ.toMeasure.real {x | x.1 ≤ 1 ∧ x.2 = 1} :=
  ⟨rfl, rfl⟩

end Concrete

/-! ### A degenerate variance: coverage is not claimed

Every subject has `(T, J, C) = (1, 0, 1)` on the grid `Fin 2`. The at-risk mass at the horizon
`m = 1` is `1`, so the joint CLT applies, but every influence coordinate has variance `0`, so the
nondegeneracy hypothesis fails. The estimator is then exactly its plug-in limit for every `n ≥ 1`,
and at `z = 0` the Wald interval with the consistent standard error `se = 0` covers with
probability `1`, while the nominal level is `nominalLevel 0 = 0`: the conclusion of the coverage
theorem is false without nondegeneracy. -/

section Degenerate

/-- The single subject record `(T, J, C) = (1, 0, 1)`. -/
def w₀ : (Fin 2 × Fin 1) × Fin 2 := ((1, 0), 1)

/-- The degenerate subject law. -/
noncomputable def μ₀ : Measure ((Fin 2 × Fin 1) × Fin 2) := Measure.dirac w₀

/-- The constant subjects on the one-point sample space. -/
def W₀ : ℕ → Unit → (Fin 2 × Fin 1) × Fin 2 := fun _ _ => w₀

/-- The at-risk mass at the horizon `1` is `1`, so the positivity hypothesis of the CLT holds. -/
theorem causeAtRiskMass_μ₀ : causeAtRiskMass μ₀ 1 = 1 := by
  simp [causeAtRiskMass, μ₀, w₀, Measure.real]

/-- Every asymptotic variance vanishes: the nondegeneracy hypothesis fails at every coordinate. -/
theorem asymVar_μ₀ (a : Coord 2 1 1) : asymVar μ₀ 1 a = 0 := by
  simp [asymVar, μ₀]

example (a : Coord 2 1 1) : ¬ 0 < asymVar μ₀ 1 a := by rw [asymVar_μ₀]; exact lt_irrefl 0

/-- The constant subjects are i.i.d. with law `μ₀`. -/
theorem hasLaw_W₀ (i : ℕ) : HasLaw (W₀ i) μ₀ (Measure.dirac ()) where
  aemeasurable := Measurable.of_discrete.aemeasurable
  map_eq := by simp [W₀, μ₀]

theorem iIndepFun_W₀ : iIndepFun W₀ (Measure.dirac ()) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases h : ∀ i ∈ S, w₀ ∈ sets i
  · have hall : (⋂ i ∈ S, W₀ i ⁻¹' sets i) = Set.univ := by
      ext u
      simp only [Set.mem_iInter, Set.mem_preimage, W₀, Set.mem_univ, iff_true]
      exact h
    rw [hall, measure_univ]
    refine (Finset.prod_eq_one fun i hi => ?_).symm
    have : W₀ i ⁻¹' sets i = Set.univ := Set.eq_univ_of_forall fun _ => h i hi
    rw [this, measure_univ]
  · simp only [not_forall] at h
    obtain ⟨i, hi, hni⟩ := h
    have hempty : W₀ i ⁻¹' sets i = ∅ := Set.eq_empty_of_forall_notMem fun _ => hni
    have hinter : (⋂ j ∈ S, W₀ j ⁻¹' sets j) = ∅ :=
      Set.eq_empty_of_subset_empty fun u hu => by
        rw [← hempty]
        exact Set.mem_iInter₂.1 hu i hi
    rw [hinter, measure_empty]
    exact (Finset.prod_eq_zero hi (by rw [hempty, measure_empty])).symm

/-- The mean cell vector of the point-mass law is the cell vector of its atom. -/
theorem cellMean_μ₀ : cellMean μ₀ = cellVector w₀ := by
  ext c
  rcases c with ⟨j, c⟩ | j <;>
    simp [cellMean, cellVector, causeEventMass, causeAtRiskMass, μ₀, Measure.real,
      Set.indicator] <;> split_ifs <;> simp

/-- For `n ≥ 1` the estimator is exactly its plug-in limit. -/
theorem estimator_W₀ {n : ℕ} (hn : n ≠ 0) (u : Unit) :
    estimator 1 (empiricalCauseData W₀ n u) = ajMap 1 (cellMean μ₀) := by
  rw [← ajMap_empiricalMean, cellMean_μ₀]
  congr 1
  simp only [empiricalMean, W₀, sum_const, card_range]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_smul]

/-- **Coverage is `1`, not the nominal level.** For every coordinate `a`, at `z = 0` with the
consistent standard error `se = √(asymVar μ₀ 1 a) = 0`, the Wald interval covers the plug-in
limit with probability `1` for every `n ≥ 1`. -/
theorem coverage_W₀ (a : Coord 2 1 1) {n : ℕ} (hn : n ≠ 0) :
    (Measure.dirac ()).real {u : Unit | ajMap 1 (cellMean μ₀) a ∈
      waldInterval (estimator 1 (empiricalCauseData W₀ n u) a)
        (√(asymVar μ₀ 1 a) / √(n : ℝ)) 0} = 1 := by
  have h : {u : Unit | ajMap 1 (cellMean μ₀) a ∈
      waldInterval (estimator 1 (empiricalCauseData W₀ n u) a)
        (√(asymVar μ₀ 1 a) / √(n : ℝ)) 0} = Set.univ :=
    Set.eq_univ_of_forall fun u => by
      rw [Set.mem_ofPred_eq, estimator_W₀ hn u, mem_waldInterval_iff]
      simp
  rw [h, probReal_univ]

/-- So, with all hypotheses of `tendsto_coverage_waldInterval_estimator` except nondegeneracy
(i.i.d. subjects, positive at-risk mass, a consistent standard error), the coverage does **not**
tend to the nominal level `nominalLevel 0 = 0`. -/
example (a : Coord 2 1 1) :
    iIndepFun W₀ (Measure.dirac ()) ∧ (∀ i, HasLaw (W₀ i) μ₀ (Measure.dirac ())) ∧
      causeAtRiskMass μ₀ 1 ≠ 0 ∧ asymVar μ₀ 1 a = 0 ∧
      ¬ Tendsto (fun n : ℕ => (Measure.dirac ()).real {u : Unit | ajMap 1 (cellMean μ₀) a ∈
          waldInterval (estimator 1 (empiricalCauseData W₀ n u) a)
            (√(asymVar μ₀ 1 a) / √(n : ℝ)) 0})
        atTop (𝓝 (nominalLevel 0)) := by
  refine ⟨iIndepFun_W₀, hasLaw_W₀, by rw [causeAtRiskMass_μ₀]; norm_num, asymVar_μ₀ a,
    fun hT => ?_⟩
  have h1 : Tendsto (fun n : ℕ => (Measure.dirac ()).real {u : Unit | ajMap 1 (cellMean μ₀) a ∈
      waldInterval (estimator 1 (empiricalCauseData W₀ n u) a)
        (√(asymVar μ₀ 1 a) / √(n : ℝ)) 0}) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ne_atTop 0] with n hn
      exact (coverage_W₀ a hn).symm)
  have := tendsto_nhds_unique hT h1
  rw [nominalLevel_zero] at this
  norm_num at this

end Degenerate

end MathlibExtTest.Probability.Statistics.FixedGridIntervals
