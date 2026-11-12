/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.ProcessAsymptotics

/-!
# Tests for the process-level survival limits

* Grid step paths: values at the grid times, including the start (`0`) and the horizon (`τ`).
* Nelson–Aalen increments: on the risk set the error and martingale increments agree; with an
  empty risk set and a positive hazard they differ (so the support hypothesis is needed).
* Concrete Kaplan–Meier and Aalen–Johansen values through the grid maps, the single-cause
  reduction of Aalen–Johansen to `1 - Ŝ`, and `ajDeriv` at `x = 0` (cumulative sums).
* A satisfiable instance of the J1 Nelson–Aalen theorem (all hypotheses discharged, degenerate
  data), and satisfiable instances of the Kaplan–Meier and Aalen–Johansen grid theorems.
* The covariance theorems applied in boundary cases.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open MathlibExt.Probability.Statistics.ProcessAsymptotics MathlibExt.Probability.Martingale
open MathlibExt.Probability.Statistics.CountingProcess (nelsonAalenProcess stochasticIntegral
  aalenCompensator)
open MathlibExt.Probability.Statistics.FunctionalDelta (prodIntegral duhamelDeriv gridIncrements)
open scoped ENNReal NNReal

namespace MathlibExtTest.Probability.Statistics.Survival.ProcessAsymptotics

/-! ### Grid step paths -/

example (a b : ℝ) : gridPath 1 2 ![a, b] (gridTime zero_le_one 2 0 (by norm_num)) = 0 := by
  rw [gridPath_apply_gridTime one_pos]
  simp

example (a b : ℝ) : gridPath 1 2 ![a, b] (gridTime zero_le_one 2 1 (by norm_num)) = a := by
  rw [gridPath_apply_gridTime one_pos]
  simp [Finset.sum_filter]

/-- At the horizon `τ = 2 τ / 2` the step path has collected every increment. -/
example (a b : ℝ) : gridPath 1 2 ![a, b] (gridTime zero_le_one 2 2 le_rfl) = a + b := by
  rw [gridPath_apply_gridTime one_pos]
  simp [Finset.sum_filter, Fin.sum_univ_two]

example (y z : Fin 3 → ℝ) : edist (gridPath 2 3 y) (gridPath 2 3 z) ≤ 3 * edist y z := by
  simpa using lipschitzWith_gridPath 2 3 y z

/-! ### Nelson–Aalen increments and paths -/

/-- One death per step among one subject at risk, hazard increments `1/2`: the error increment
`√n (1 - 1/2)` equals the martingale increment. -/
example (n i : ℕ) :
    naErrorIncrement n (fun k (_ : Unit) => (k : ℝ)) (fun _ _ => 1) (fun k => (k : ℝ) / 2) i () =
      naMartingaleIncrement n (fun k (_ : Unit) => (k : ℝ)) (fun _ _ => 1)
        (fun k => (k : ℝ) / 2) i () :=
  naErrorIncrement_eq_naMartingaleIncrement (by norm_num)

/-- **The support hypothesis is needed**: with nobody at risk and a unit hazard increment, the
error increment is `-√n · 1 = -1` (for `n = 1`) while the martingale increment is `0`. -/
example :
    naErrorIncrement 1 (fun _ (_ : Unit) => (0 : ℝ)) (fun _ _ => 0) (fun k => (k : ℝ)) 0 () = -1 ∧
      naMartingaleIncrement 1 (fun _ (_ : Unit) => (0 : ℝ)) (fun _ _ => 0)
        (fun k => (k : ℝ)) 0 () = 0 := by
  simp [naErrorIncrement, naMartingaleIncrement, nelsonAalenProcess, stochasticIntegral]

/-- The error path at a grid time is `√n (Â_k - (α_k - α_0))`. -/
example (n : ℕ) :
    naErrorPath 1 2 n (fun k (_ : Unit) => (k : ℝ)) (fun _ _ => 1) (fun k => (k : ℝ) / 2) ()
        (gridTime zero_le_one 2 2 le_rfl) = √(n : ℝ) * (2 - 1) := by
  rw [naErrorPath_apply_gridTime one_pos]
  simp [nelsonAalenProcess, stochasticIntegral]

example (n : ℕ) :
    naErrorPath 1 3 n (fun k (_ : Unit) => (k : ℝ)) (fun _ _ => 2) (fun k => (k : ℝ) / 2) () =
      naMartingalePath 1 3 n (fun k (_ : Unit) => (k : ℝ)) (fun _ _ => 2)
        (fun k => (k : ℝ) / 2) () :=
  naErrorPath_eq_naMartingalePath fun _ _ => by norm_num

/-! ### A satisfiable instance of the J1 Nelson–Aalen theorem -/

/-- Degenerate data (no deaths, one subject at risk, zero hazard) on `[0, 1]`: every hypothesis
of `tendstoInDistribution_naErrorPath` is discharged, including tightness and the support
condition, and the conclusion is J1 convergence to the zero path. -/
example :
    TendstoInDistribution
      (fun n => naErrorPath 1 1 n (fun _ (_ : Unit) => (0 : ℝ)) (fun _ _ => 1) (fun _ => 0))
      atTop (fun _ : Unit => SkorokhodSpace.ofContinuous 0)
      (fun _ => Measure.dirac ()) (Measure.dirac ()) := by
  have hpath : ∀ n (ω : Unit) t, naMartingalePath 1 1 n (fun _ (_ : Unit) => (0 : ℝ))
      (fun _ _ => 1) (fun _ => 0) ω t = 0 := by
    intro n ω t
    have hinc : ∀ i, naMartingaleIncrement n (fun _ (_ : Unit) => (0 : ℝ)) (fun _ _ => 1)
        (fun _ => 0) i ω = 0 := by
      intro i
      simp [naMartingaleIncrement, aalenCompensator, stochasticIntegral]
    change gridPathFun 1 1 (fun i => naMartingaleIncrement n (fun _ (_ : Unit) => (0 : ℝ))
      (fun _ _ => 1) (fun _ => 0) i ω) t = 0
    simp [gridPathFun, hinc]
  refine tendstoInDistribution_naErrorPath (τ := 1) one_pos (fun _ => 1)
    (fun _ _ _ => 0) (fun _ _ _ => 1) (fun _ _ => 0) (fun _ _ => measurable_const)
    (fun _ _ => measurable_const) ?_ (fun _ _ => 0) (fun _ => 0) (fun _ => aemeasurable_const)
    aemeasurable_const ?_ ?_ ?_
  · simp
  · rw [Set.range_const, isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε _
    refine ⟨{0}, isCompact_singleton, fun μ hμ => ?_⟩
    rw [Set.mem_singleton_iff] at hμ
    subst hμ
    rw [Measure.map_const, measure_univ, one_smul,
      Measure.dirac_apply' _ isClosed_singleton.measurableSet.compl]
    simp
  · intro I
    exact tendstoInDistribution_const (l := atTop) aemeasurable_const
  · intro ε hε
    refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, by simp, fun n ω _ t => ?_⟩
    rw [hpath]
    simp [hε.le]

/-- The time-changed Brownian corollary, applied (hypotheses as variables). -/
example {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {τ : ℝ} (hτ : 0 < τ)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsPreBrownianReal B P') {σsq : Set.Icc (0 : ℝ) τ → ℝ≥0}
    (hσ : Monotone σsq) {Z : Ω' → C(Set.Icc (0 : ℝ) τ, ℝ)}
    (hZB : ∀ᵐ ω' ∂P', ∀ t, Z ω' t = B (σsq t) ω') :
    cov[fun ω' => Z ω' ⟨0, le_rfl, hτ.le⟩, fun ω' => Z ω' ⟨τ, hτ.le, le_rfl⟩; P'] =
      σsq ⟨0, le_rfl, hτ.le⟩ := by
  rw [covariance_timeChangedBrownian hB hσ hZB]
  congr
  exact min_eq_left (Subtype.mk_le_mk.2 hτ.le)

/-! ### Kaplan–Meier on the grid -/

/-- One step, one death among two at risk: `Ŝ_1 = 1/2`, via the product-integral bridge. -/
example : kmGridVector 1 (fun k (_ : Unit) => (k : ℝ)) (fun _ _ => 2) () 0 = 1 / 2 := by
  rw [kmGridVector_eq_prodIntegral]
  have h : Iic (0 : Fin 1) = {0} := by decide
  simp [prodIntegral, h, gridIncrements_naGridVector, nelsonAalenProcess,
    stochasticIntegral]
  norm_num

example : naGridVector 2 (fun k (_ : Unit) => (k : ℝ)) (fun _ _ => 2) () 1 = 1 := by
  simp [naGridVector, nelsonAalenProcess, stochasticIntegral]

/-- The closed Greenwood form of the Kaplan–Meier limit functional, one grid point. -/
example (x h : Fin 1 → ℝ) (hx : 1 + x 0 ≠ 0) :
    (-duhamelDeriv x h) 0 = -h 0 := by
  rw [neg_duhamelDeriv_apply_eq_sum x h (fun i => by fin_cases i; exact hx)]
  have h1 : Iic (0 : Fin 1) = {0} := by decide
  simp [h1, prodIntegral, hx]

/-- The Kaplan–Meier grid theorem has satisfiable hypotheses: with no deaths the Nelson–Aalen
vector is `0`, and the conclusion is convergence to `0`. -/
example (v : Fin 2 → ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • (kmGridVector 2 (fun _ (_ : Fin 2 → ℝ) => (0 : ℝ))
        (fun _ _ => 1) ω - prodIntegral (-gridIncrements 0)))
      atTop (fun _ => -duhamelDeriv (-gridIncrements 0)
        (gridIncrements (0 : Fin 2 → ℝ)))
      (fun _ => Measure.dirac v) (Measure.dirac v) :=
  tendstoInDistribution_kmGridVector (fun _ _ _ => 0) (fun _ _ _ => 1) (Λ := 0) (G := fun _ => 0)
    ((tendstoInDistribution_const (l := atTop) (Z := (0 : (Fin 2 → ℝ) → Fin 2 → ℝ))
      aemeasurable_const).congr (fun n => ae_of_all _ fun ω => by
        ext j
        simp [naGridVector, nelsonAalenProcess, stochasticIntegral])
      (ae_of_all _ fun _ => rfl))

/-- Boundary case of the covariance theorems: deterministic (zero) increments have zero
variance, and both the Nelson–Aalen and Greenwood covariances vanish. -/
example (Λ : Fin 2 → ℝ) (hΛ : ∀ i, gridIncrements Λ i ≠ 1) (a b : Fin 2) :
    cov[fun _ : Unit => (-duhamelDeriv (-gridIncrements Λ)
        (0 : Fin 2 → ℝ)) a,
      fun _ => (-duhamelDeriv (-gridIncrements Λ)
        (0 : Fin 2 → ℝ)) b; Measure.dirac ()] = 0 := by
  rw [covariance_kmGridLimit (P' := Measure.dirac ()) Λ (fun _ => 0) 0
    (fun _ => memLp_const 0) (fun _ _ => by simp) hΛ]
  simp

example (a b : Fin 3) :
    cov[fun _ : Unit => ∑ _i ∈ Iic a, (0 : ℝ), fun _ => ∑ _i ∈ Iic b, (0 : ℝ);
      Measure.dirac ()] = ∑ i ∈ Iic (min a b), (0 : Fin 3 → ℝ) i :=
  covariance_naGridLimit (fun _ _ => 0) 0 (fun _ => memLp_const 0)
    (fun _ _ => by simp) a b

/-! ### Aalen–Johansen on the grid -/

/-- Two grid points, one cause: `F(t₁) = a + (1 - a) b`, the complement of the Kaplan–Meier
survival `(1 - a)(1 - b)`. -/
example (a b : ℝ) : ajIncidence ![![a], ![b]] 1 0 = a + (1 - a) * b := by
  have h1 : Iic (1 : Fin 2) = {0, 1} := by decide
  have h2 : Iio (0 : Fin 2) = ∅ := by decide
  have h3 : Iio (1 : Fin 2) = {0} := by decide
  simp [ajIncidence, h1, h2, h3]

/-- Two causes at one grid point: each cause contributes its own hazard increment. -/
example (a b : ℝ) : ajIncidence ![![a, b]] 0 1 = b := by
  have h1 : Iic (0 : Fin 1) = {0} := by decide
  simp [ajIncidence, h1]

/-- At `x = 0` the Aalen–Johansen derivative is the cumulative sum of the perturbation. -/
example {K r : ℕ} (h : Fin K → Fin r → ℝ) (j : Fin K) (c : Fin r) :
    ajDeriv 0 h j c = ∑ i ∈ Iic j, h i c := by
  simp [ajDeriv_apply]

example (i : Fin 2) (c : Fin 3) (y : Fin 2 → Fin 3 → ℝ) : ajCoord i c y = y i c := rfl

open MathlibExt.Probability.Statistics.CompetingRisks in
/-- One grid time, one failure of cause `0` and one censoring among two at risk:
`F̂_0(t₀) = 1/2`, via the grid-map bridge. -/
example : let D : CompetingRiskData 1 1 :=
      ⟨fun _ => 0, Subsingleton.strictMono _, fun _ _ => 1, fun _ => 1⟩
    D.cumulativeIncidence 0 (D.time 0) = 1 / 2 := by
  intro D
  rw [cumulativeIncidence_time_eq_ajIncidence]
  have hr : D.atRisk 0 = 2 := by decide
  have h1 : Iic (0 : Fin 1) = {0} := by decide
  have h2 : Iio (0 : Fin 1) = ∅ := by decide
  simp [ajIncidence, h1, h2, hr, D]

/-- The Aalen–Johansen grid theorem has satisfiable hypotheses (constant hazard estimates). -/
example (v : Fin 2 → ℝ) (x : Fin 2 → Fin 3 → ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) (_ : Fin 2 → ℝ) => √(n : ℝ) • (ajIncidence x - ajIncidence x))
      atTop (fun _ => ajDeriv x 0) (fun _ => Measure.dirac v) (Measure.dirac v) :=
  tendstoInDistribution_ajIncidence (xhat := fun _ _ => x) (G := fun _ => 0)
    ((tendstoInDistribution_const (l := atTop) aemeasurable_const).congr
      (fun n => ae_of_all _ fun ω => by simp) (ae_of_all _ fun _ => rfl))

/-- Boundary case of the Aalen–Johansen covariance: zero variances give zero covariance. -/
example (x : Fin 2 → Fin 2 → ℝ) (j j' : Fin 2) (c c' : Fin 2) :
    cov[fun _ : Unit => ajDeriv x 0 j c, fun _ => ajDeriv x 0 j' c'; Measure.dirac ()] = 0 := by
  rw [covariance_ajLimit (P' := Measure.dirac ()) x (fun _ => 0) 0 (fun _ => memLp_const 0)
    (fun _ _ => by simp)]
  simp

end MathlibExtTest.Probability.Statistics.Survival.ProcessAsymptotics
