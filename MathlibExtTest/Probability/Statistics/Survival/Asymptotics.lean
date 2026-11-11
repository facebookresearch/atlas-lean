/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.Asymptotics
public import MathlibExtTest.Probability.Statistics.Survival.Consistency
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter Topology RealInnerProductSpace
open MathlibExt.Probability.Statistics.Censoring
open MathlibExt.Probability.Statistics.KaplanMeier
open MathlibExt.Probability.Statistics.SurvivalConsistency
open MathlibExt.Probability.Statistics.SurvivalAsymptotics
open MathlibExtTest.Probability.Statistics.SurvivalConsistency

namespace MathlibExtTest.Probability.Statistics.SurvivalAsymptotics

/-! ### Cells -/

/-- `(T, C) = (1, 0)` is censored at `0`; `(1, 1)` is an event at `1` (a tie counts as an event). -/
example : cell ((1 : Fin 2), (0 : Fin 2)) = (0, false) ∧
    cell ((1 : Fin 2), (1 : Fin 2)) = (1, true) := by decide

/-- The cell indicator vector has a single `1`. -/
example : cellVec ((1 : Fin 2), (0 : Fin 2)) (0, false) = 1 ∧
    cellVec ((1 : Fin 2), (0 : Fin 2)) (0, true) = 0 := by
  simp [cellVec, cell]

/-- At the cell probabilities of the `Fin 2` fixture, the at-risk functional at `1` is
`P(min T C ≥ 1) = 3/8`. -/
example : cellAtRisk 1 (cellProbs (indepLaw pT2 pC2)) = 3 / 8 := by
  rw [cellAtRisk_cellProbs, obsAtRiskMass_pT2_pC2]

/-! ### The Kaplan–Meier map -/

/-- On the `Fin 2` fixture, the Kaplan–Meier map at the cell probabilities at `m = 0` is
`P(T > 0) = P(T ≥ 1) = 3/4`. -/
example : kmMap 0 (cellProbs (indepLaw pT2 pC2)) = 3 / 4 := by
  have hm : obsAtRiskMass (indepLaw pT2 pC2) 0 ≠ 0 := by
    rw [obsAtRiskMass_indepLaw, survivalMass_pT2.1, survivalMass_pC2.1]; norm_num
  rw [kmMap_cellProbs_indepLaw pT2 pC2 0 hm, ← survivalMass_pT2.2, survivalMass]
  congr 1


/-- At the empirical proportions, `kmMap` is the Kaplan–Meier estimate, for any sample. -/
example (Z : ℕ → Unit → Fin 2 × Fin 2) (n : ℕ) :
    kmMap 1 (cellProportions Z n ()) = (empiricalData Z n ()).kmSurvival ((1 : ℕ) : ℝ) :=
  kmMap_cellProportions 1 n ()

/-- The derivative vanishes at the base point. -/
example : kmMapDeriv 1 (cellProbs (indepLaw pT2 pC2)) (cellProbs (indepLaw pT2 pC2)) = 0 :=
  kmMapDeriv_self _ _

/-! ### The central limit theorems on the canonical sequence space -/

/-- Deliverable 1 on the canonical sequence space of the `Fin 2` fixture. -/
example : ∃ A : CellSpace 2 →L[ℝ] CellSpace 2, HasGaussianLaw A (stdGaussian (CellSpace 2)) ∧
    (∀ t : CellSpace 2, HasLaw (fun z ↦ ⟪A z, t⟫)
      (gaussianReal 0 (Var[fun z ↦ ⟪cellVec z, t⟫; indepLaw pT2 pC2]).toNNReal)
      (stdGaussian (CellSpace 2))) ∧
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) •
        (cellProportions (fun i ω => ω i) n ω - cellProbs (indepLaw pT2 pC2)))
      atTop A (fun _ ↦ Measure.infinitePi fun _ : ℕ => indepLaw pT2 pC2)
      (stdGaussian (CellSpace 2)) :=
  exists_tendstoInDistribution_cellProportions
    (iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id)
    (fun i => (measurePreserving_eval_infinitePi (fun _ : ℕ => indepLaw pT2 pC2) i).hasLaw)

/-- Deliverable 2 at `m = 0` on the `Fin 2` fixture: `√n (Ŝₙ(0) - 3/4) →ᵈ L A`. -/
example : ∃ A : CellSpace 2 →L[ℝ] CellSpace 2, HasGaussianLaw A (stdGaussian (CellSpace 2)) ∧
    (∀ t : CellSpace 2, HasLaw (fun z ↦ ⟪A z, t⟫)
      (gaussianReal 0 (Var[fun z ↦ ⟪cellVec z, t⟫; indepLaw pT2 pC2]).toNNReal)
      (stdGaussian (CellSpace 2))) ∧
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) •
        ((empiricalData (fun i ω => ω i) n ω).kmSurvival ((0 : ℕ) : ℝ) -
          pT2.toMeasure.real {t | (0 : Fin 2) < t}))
      atTop (fun z ↦ kmMapDeriv 0 (cellProbs (indepLaw pT2 pC2)) (A z))
      (fun _ ↦ Measure.infinitePi fun _ : ℕ => indepLaw pT2 pC2)
      (stdGaussian (CellSpace 2)) :=
  exists_tendstoInDistribution_kmSurvival pT2 pC2
    (iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id)
    (fun i => (measurePreserving_eval_infinitePi (fun _ : ℕ => indepLaw pT2 pC2) i).hasLaw) 0
    (by rw [obsAtRiskMass_indepLaw, survivalMass_pT2.1, survivalMass_pC2.1]; norm_num)

/-! ### Variance identification and studentization -/

/-- On the `Fin 2` fixture, the population Greenwood sum at `m = 0` is
`e₀ / (Y₀ (Y₀ - e₀)) = (1/4) / (1 · 3/4) = 1/3`. -/
theorem greenwoodSum_pT2_pC2 : greenwoodSum 0 (cellProbs (indepLaw pT2 pC2)) = 1 / 3 := by
  rw [greenwoodSum_cellProbs]
  have hfilter : ({j | j ≤ (0 : Fin 2)} : Finset (Fin 2)) = {0} := by decide
  rw [hfilter, sum_singleton, obsEventMass_indepLaw, obsAtRiskMass_indepLaw, survivalMass_pT2.1,
    survivalMass_pC2.1]
  simp [pT2]
  norm_num

/-- The variance algebra at the `Fin 2` fixture, `m = 0`: the limit variance is
`S² τ² = (3/4)² · 1/3 = 3/16`. -/
example : Var[fun z ↦ kmMapDeriv 0 (cellProbs (indepLaw pT2 pC2)) (cellVec z); indepLaw pT2 pC2] =
    3 / 16 := by
  have hm : obsAtRiskMass (indepLaw pT2 pC2) 0 ≠ 0 := by
    rw [obsAtRiskMass_indepLaw, survivalMass_pT2.1, survivalMass_pC2.1]; norm_num
  have hS : kmMap 0 (cellProbs (indepLaw pT2 pC2)) = 3 / 4 := by
    rw [kmMap_cellProbs_indepLaw pT2 pC2 0 hm, ← survivalMass_pT2.2, survivalMass]
    congr 1
  rw [variance_kmMapDeriv_cellVec _ 0 hm (by rw [hS]; norm_num), hS, greenwoodSum_pT2_pC2]
  norm_num

/-- The studentized Kaplan–Meier limit at `m = 0` on the canonical sequence space of the `Fin 2`
fixture, with the constructed Gaussian limit, is standard normal. -/
example : ∃ A : CellSpace 2 →L[ℝ] CellSpace 2,
    HasLaw (fun z ↦ kmMapDeriv 0 (cellProbs (indepLaw pT2 pC2)) (A z) /
        √(pT2.toMeasure.real {t | (0 : Fin 2) < t} ^ 2 *
          greenwoodSum 0 (cellProbs (indepLaw pT2 pC2))))
      (gaussianReal 0 1) (stdGaussian (CellSpace 2)) ∧
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) •
        ((empiricalData (fun i ω => ω i) n ω).kmSurvival ((0 : ℕ) : ℝ) -
          pT2.toMeasure.real {t | (0 : Fin 2) < t}) /
          √(n * (empiricalData (fun i ω => ω i) n ω).greenwoodVariance ((0 : ℕ) : ℝ)))
      atTop (fun z ↦ kmMapDeriv 0 (cellProbs (indepLaw pT2 pC2)) (A z) /
        √(pT2.toMeasure.real {t | (0 : Fin 2) < t} ^ 2 *
          greenwoodSum 0 (cellProbs (indepLaw pT2 pC2))))
      (fun _ ↦ Measure.infinitePi fun _ : ℕ => indepLaw pT2 pC2)
      (stdGaussian (CellSpace 2)) := by
  have hm : obsAtRiskMass (indepLaw pT2 pC2) 0 ≠ 0 := by
    rw [obsAtRiskMass_indepLaw, survivalMass_pT2.1, survivalMass_pC2.1]; norm_num
  have h34 : pT2.toMeasure.real {t | (0 : Fin 2) < t} = 3 / 4 := by
    rw [← survivalMass_pT2.2, survivalMass]
    congr 1
  have hS : pT2.toMeasure.real {t | (0 : Fin 2) < t} ≠ 0 := by rw [h34]; norm_num
  have hτ : 0 < greenwoodSum 0 (cellProbs (indepLaw pT2 pC2)) := by
    rw [greenwoodSum_pT2_pC2]; norm_num
  have hind : iIndepFun (fun i (ω : ℕ → Fin 2 × Fin 2) => ω i)
      (Measure.infinitePi fun _ : ℕ => indepLaw pT2 pC2) :=
    iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
  have hlaw := fun i =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => indepLaw pT2 pC2) i).hasLaw
  obtain ⟨A, -, hA, -⟩ := exists_tendstoInDistribution_cellProportions hind hlaw
  exact ⟨A, hasLaw_studentized_limit pT2 pC2 0 hm hS hτ hA,
    tendstoInDistribution_kmSurvival_studentized pT2 pC2 hind hlaw 0 hm hS hτ
      A.continuous.aemeasurable hA⟩

end MathlibExtTest.Probability.Statistics.SurvivalAsymptotics
