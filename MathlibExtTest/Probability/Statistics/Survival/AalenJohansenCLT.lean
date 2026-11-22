/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.AalenJohansenCLT
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter
open MathlibExt.Probability.Statistics.Censoring
open MathlibExt.Probability.Statistics.CompetingRisks
open MathlibExt.Probability.Statistics.SurvivalConsistency
open MathlibExt.Probability.Statistics.AalenJohansenCLT

namespace MathlibExtTest.Probability.Statistics.AalenJohansenCLT

/-- The independent-censoring law is a probability measure (local instance for the examples). -/
private theorem isProbabilityMeasure_indepCauseLaw {k r : ℕ} (pTJ : PMF (Fin k × Fin r))
    (pC : PMF (Fin k)) : IsProbabilityMeasure (indepCauseLaw pTJ pC) := by
  unfold indepCauseLaw; infer_instance

attribute [local instance] isProbabilityMeasure_indepCauseLaw

/-! ### Cells, cell vectors and the cell mean -/

/-- `Cell 2 3` has `2 · 3` event cells and `2` at-risk cells. -/
example : Fintype.card (Cell 2 3) = 8 := by simp

/-- `Coord 3 2 1` has the Kaplan–Meier row and `2` cause rows at the grid indices `0, 1`. -/
example : Fintype.card (Coord 3 2 (1 : Fin 3)) = 6 := by decide

/-- A subject with `(T, J, C) = (1, 0, 2)` fails from cause `0` at grid index `1`: its event cell
`(1, 0)` is `1`, it is at risk at `1`, and not at risk at `2`. -/
example :
    cellVector (((1 : Fin 3), (0 : Fin 2)), (2 : Fin 3)) (Sum.inl (1, 0)) = 1 ∧
      cellVector (((1 : Fin 3), (0 : Fin 2)), (2 : Fin 3)) (Sum.inl (1, 1)) = 0 ∧
      cellVector (((1 : Fin 3), (0 : Fin 2)), (2 : Fin 3)) (Sum.inr 1) = 1 ∧
      cellVector (((1 : Fin 3), (0 : Fin 2)), (2 : Fin 3)) (Sum.inr 2) = 0 := by
  simp [cellVector]

/-- A censored subject `(T, J, C) = (2, 1, 0)` has no event cell and is at risk only at `0`. -/
example :
    cellVector (((2 : Fin 3), (1 : Fin 2)), (0 : Fin 3)) (Sum.inl (0, 1)) = 0 ∧
      cellVector (((2 : Fin 3), (1 : Fin 2)), (0 : Fin 3)) (Sum.inr 0) = 1 := by
  simp [cellVector]

/-- The cell mean has the cause-specific event masses and the at-risk masses as coordinates. -/
example (μ : Measure ((Fin 3 × Fin 2) × Fin 3)) (j : Fin 3) (c : Fin 2) :
    cellMean μ (Sum.inl (j, c)) = causeEventMass μ j c ∧
      cellMean μ (Sum.inr j) = causeAtRiskMass μ j :=
  ⟨rfl, rfl⟩

/-! ### The Aalen–Johansen map -/

/-- On the zero cell vector every factor is `1` (Lean's `x / 0 = 0`). -/
example (l : Fin 3) : factor (0 : EuclideanSpace ℝ (Cell 3 2)) l = 1 := by simp [factor]

/-- Two subjects at risk at `0`, one of whom fails from cause `0` there: the Kaplan–Meier factor
is `1 - 1/2`. -/
example :
    factor (WithLp.toLp 2 fun i : Cell 1 1 => match i with
      | Sum.inl _ => (1 : ℝ) | Sum.inr _ => 2) 0 = 1 / 2 := by
  norm_num [factor]

/-- One grid point, one cause: the map gives `1 - d/Y` for Kaplan–Meier and `d/Y` for the
cumulative incidence (here `d = 1`, `Y = 4`). -/
example :
    ajMap (0 : Fin 1) (WithLp.toLp 2 fun i : Cell 1 1 => match i with
        | Sum.inl _ => (1 : ℝ) | Sum.inr _ => 4) (none, ⟨0, le_rfl⟩) = 3 / 4 ∧
      ajMap (0 : Fin 1) (WithLp.toLp 2 fun i : Cell 1 1 => match i with
        | Sum.inl _ => (1 : ℝ) | Sum.inr _ => 4) (some 0, ⟨0, le_rfl⟩) = 1 / 4 := by
  constructor <;> norm_num [ajMap, factor]

/-- Scale invariance of the Aalen–Johansen map. -/
example (u : EuclideanSpace ℝ (Cell 3 2)) : ajMap (2 : Fin 3) ((5 : ℝ) • u) = ajMap 2 u :=
  ajMap_smul 2 (by norm_num) u

/-- The Aalen–Johansen map is differentiable at a cell vector with nonzero at-risk coordinates. -/
example (u : EuclideanSpace ℝ (Cell 3 2)) (hu : ∀ l, u (Sum.inr l) ≠ 0) :
    DifferentiableAt ℝ (ajMap (2 : Fin 3)) u :=
  differentiableAt_ajMap 2 fun l _ => hu l

example : Measurable (ajMap (r := 2) (1 : Fin 3)) := measurable_ajMap 1

/-! ### The estimator and the empirical mean -/

/-- The estimator coordinates are the Kaplan–Meier survival and the cumulative incidence. -/
example (D : CompetingRiskData 3 2) (j : {j : Fin 3 // j ≤ 2}) (c : Fin 2) :
    estimator 2 D (none, j) = D.toCensoredData.kmSurvival (D.time j) ∧
      estimator 2 D (some c, j) = D.cumulativeIncidence c (D.time j) :=
  ⟨rfl, rfl⟩

/-- Two subjects, both `(T, J, C) = (0, 0, 0)`: the empirical at-risk proportion at `0` is `1`. -/
example : empiricalMean (fun _ (_ : Unit) => (((0 : Fin 1), (0 : Fin 1)), (0 : Fin 1))) 2 ()
    (Sum.inr 0) = 1 := by
  norm_num [empiricalMean, cellVector]

/-- Non-vacuity of the estimator identity: one subject failing from cause `0` at grid index `0`
gives the Aalen–Johansen cumulative incidence `1` and the Kaplan–Meier survival `0` there. -/
example :
    estimator (0 : Fin 1) (empiricalCauseData
        (fun _ (_ : Unit) => (((0 : Fin 1), (0 : Fin 1)), (0 : Fin 1))) 1 ())
        (some 0, ⟨0, le_rfl⟩) = 1 ∧
      estimator (0 : Fin 1) (empiricalCauseData
        (fun _ (_ : Unit) => (((0 : Fin 1), (0 : Fin 1)), (0 : Fin 1))) 1 ())
        (none, ⟨0, le_rfl⟩) = 0 := by
  rw [← ajMap_empiricalMean]
  constructor <;>
    norm_num [ajMap, factor, empiricalMean, cellVector, Finset.filter_eq', Finset.filter_eq]

/-- The summed cell vectors count the events of each cause and the subjects at risk. -/
example (W : ℕ → Unit → (Fin 3 × Fin 2) × Fin 3) (n : ℕ) :
    (∑ i ∈ range n, cellVector (W i ())) (Sum.inl (1, 0)) =
        (empiricalCauseData W n ()).events 1 0 ∧
      (∑ i ∈ range n, cellVector (W i ())) (Sum.inr 2) = (empiricalCauseData W n ()).atRisk 2 :=
  ⟨sum_cellVector_inl W n () 1 0, sum_cellVector_inr W n () 2⟩

/-! ### Identification and the estimand -/

/-- The point mass of the marginal law of `T` is the sum over causes. -/
example (pTJ : PMF (Fin 3 × Fin 2)) (l : Fin 3) :
    ((PMF.map Prod.fst pTJ) l).toReal = (pTJ (l, 0)).toReal + (pTJ (l, 1)).toReal := by
  rw [toReal_map_fst_apply, Fin.sum_univ_two]

/-- The estimand coordinates are `P(T > j)` and `P(T ≤ j, J = c)`. -/
example (pTJ : PMF (Fin 3 × Fin 2)) (j : {j : Fin 3 // j ≤ 2}) (c : Fin 2) :
    target pTJ 2 (none, j) = (PMF.map Prod.fst pTJ).toMeasure.real {t | j.1 < t} ∧
      target pTJ 2 (some c, j) = pTJ.toMeasure.real {x | x.1 ≤ j.1 ∧ x.2 = c} :=
  ⟨rfl, rfl⟩

/-- At the first grid index everyone is at risk. -/
private theorem causeAtRiskMass_zero {k r : ℕ} (pTJ : PMF (Fin (k + 1) × Fin r))
    (pC : PMF (Fin (k + 1))) :
    causeAtRiskMass (indepCauseLaw pTJ pC) 0 = 1 := by
  have hs : {ω : (Fin (k + 1) × Fin r) × Fin (k + 1) | (0 : Fin (k + 1)) ≤ min ω.1.1 ω.2} =
      Set.univ := Set.eq_univ_of_forall fun ω => Fin.zero_le _
  rw [causeAtRiskMass, hs, probReal_univ]

/-- Identification at horizon `0`: the plug-in limit is the estimand. -/
example (pTJ : PMF (Fin 3 × Fin 2)) (pC : PMF (Fin 3)) :
    ajMap (0 : Fin 3) (cellMean (indepCauseLaw pTJ pC)) = target pTJ 0 :=
  ajMap_cellMean_indepCauseLaw pTJ pC 0 (by rw [causeAtRiskMass_zero]; norm_num)

/-- With `(T, J) = (2, 0)` and `C = 2` almost surely, everyone is at risk at grid index `2`. -/
private theorem causeAtRiskMass_pure_two :
    causeAtRiskMass (indepCauseLaw (PMF.pure ((2 : Fin 3), (0 : Fin 2))) (PMF.pure (2 : Fin 3)))
      2 = 1 := by
  rw [causeAtRiskMass_indepCauseLaw_eq, PMF.pure_map]
  simp [survivalMass, PMF.toMeasure_pure]

/-- Identification at horizon `2`, where the Kaplan–Meier product and the cumulative-incidence
sum run over three grid indices: the cause-`0` cumulative incidence at `2` is
`P(T ≤ 2, J = 0) = 1`. -/
example :
    ajMap (2 : Fin 3) (cellMean (indepCauseLaw (PMF.pure ((2 : Fin 3), (0 : Fin 2)))
      (PMF.pure (2 : Fin 3)))) (some 0, ⟨2, le_rfl⟩) = 1 := by
  rw [ajMap_cellMean_indepCauseLaw _ _ 2 (by rw [causeAtRiskMass_pure_two]; norm_num)]
  simp [target, PMF.toMeasure_pure]

example (pTJ : PMF (Fin 3 × Fin 2)) (pC : PMF (Fin 3)) (l : Fin 3) :
    causeAtRiskMass (indepCauseLaw pTJ pC) l =
      survivalMass (PMF.map Prod.fst pTJ) l * survivalMass pC l :=
  causeAtRiskMass_indepCauseLaw_eq pTJ pC l

/-! ### The joint CLT on the canonical sequence space -/

section Canonical

variable (pTJ : PMF (Fin 3 × Fin 2)) (pC : PMF (Fin 3))

private lemma hasLaw_eval (i : ℕ) :
    HasLaw (fun ω : ℕ → (Fin 3 × Fin 2) × Fin 3 => ω i) (indepCauseLaw pTJ pC)
      (Measure.infinitePi fun _ : ℕ => indepCauseLaw pTJ pC) := by
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => indepCauseLaw pTJ pC) i).hasLaw

private lemma iIndep_eval :
    iIndepFun (fun i (ω : ℕ → (Fin 3 × Fin 2) × Fin 3) => ω i)
      (Measure.infinitePi fun _ : ℕ => indepCauseLaw pTJ pC) := by
  exact iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id

/-- The hypotheses of the joint CLT are satisfiable: i.i.d. coordinates of the product measure,
horizon `0` (always inside the support). The conclusion is the joint CLT centered at the
estimand. -/
example : ∃ Y : EuclideanSpace ℝ (Cell 3 2) → Coord 3 2 (0 : Fin 3) → ℝ,
    HasGaussianLaw Y (stdGaussian (EuclideanSpace ℝ (Cell 3 2))) ∧
    (∀ s : Coord 3 2 0 → ℝ, HasLaw (fun z => ∑ a, s a * Y z a)
      (gaussianReal 0 (Var[fun ω : ℕ → (Fin 3 × Fin 2) × Fin 3 =>
        ∑ a, s a * influence (indepCauseLaw pTJ pC) 0 (ω 0) a;
        Measure.infinitePi fun _ : ℕ => indepCauseLaw pTJ pC]).toNNReal)
      (stdGaussian (EuclideanSpace ℝ (Cell 3 2)))) ∧
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) •
        (estimator 0 (empiricalCauseData (fun i ω => ω i) n ω) - target pTJ 0))
      atTop Y (fun _ => Measure.infinitePi fun _ : ℕ => indepCauseLaw pTJ pC)
      (stdGaussian (EuclideanSpace ℝ (Cell 3 2))) := by
  exact tendstoInDistribution_estimator_indepCauseLaw pTJ pC (iIndep_eval pTJ pC)
    (hasLaw_eval pTJ pC) 0 (by rw [causeAtRiskMass_zero]; norm_num)

/-- The covariance of the joint limit between the Kaplan–Meier coordinate and the cause-`1`
cumulative incidence at grid index `0` is the covariance of the influence coordinates. -/
example : ∃ Y : EuclideanSpace ℝ (Cell 3 2) → Coord 3 2 (0 : Fin 3) → ℝ,
    cov[fun z => Y z (none, ⟨0, le_rfl⟩), fun z => Y z (some 1, ⟨0, le_rfl⟩);
        stdGaussian (EuclideanSpace ℝ (Cell 3 2))] =
      cov[fun ω : ℕ → (Fin 3 × Fin 2) × Fin 3 =>
          influence (indepCauseLaw pTJ pC) 0 (ω 0) (none, ⟨0, le_rfl⟩),
        fun ω => influence (indepCauseLaw pTJ pC) 0 (ω 0) (some 1, ⟨0, le_rfl⟩);
        Measure.infinitePi fun _ : ℕ => indepCauseLaw pTJ pC] := by
  obtain ⟨Y, -, hY, -⟩ := tendstoInDistribution_estimator (iIndep_eval pTJ pC)
    (hasLaw_eval pTJ pC) 0 (by rw [causeAtRiskMass_zero]; norm_num)
  have hW : AEMeasurable (fun ω : ℕ → (Fin 3 × Fin 2) × Fin 3 => ω 0)
      (Measure.infinitePi fun _ : ℕ => indepCauseLaw pTJ pC) := (measurable_pi_apply 0).aemeasurable
  exact ⟨Y, covariance_limit (W := fun i (ω : ℕ → (Fin 3 × Fin 2) × Fin 3) => ω i) 0 hY hW
    (none, ⟨0, le_rfl⟩) (some 1, ⟨0, le_rfl⟩)⟩

/-- The Kaplan–Meier marginal at grid index `0`, derived from the joint theorem. -/
example : ∃ Z : EuclideanSpace ℝ (Cell 3 2) → ℝ,
    HasLaw Z (gaussianReal 0 (Var[fun ω : ℕ → (Fin 3 × Fin 2) × Fin 3 =>
        influence (indepCauseLaw pTJ pC) 0 (ω 0) (none, ⟨0, le_rfl⟩);
        Measure.infinitePi fun _ : ℕ => indepCauseLaw pTJ pC]).toNNReal)
      (stdGaussian (EuclideanSpace ℝ (Cell 3 2))) ∧
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) *
        ((empiricalCauseData (fun i ω => ω i) n ω).toCensoredData.kmSurvival ((0 : ℕ) : ℝ) -
          (PMF.map Prod.fst pTJ).toMeasure.real {t | (0 : Fin 3) < t}))
      atTop Z (fun _ => Measure.infinitePi fun _ : ℕ => indepCauseLaw pTJ pC)
      (stdGaussian (EuclideanSpace ℝ (Cell 3 2))) := by
  exact tendstoInDistribution_kmSurvival_indepCauseLaw pTJ pC (iIndep_eval pTJ pC)
    (hasLaw_eval pTJ pC) 0 (by rw [causeAtRiskMass_zero]; norm_num) 0 le_rfl

/-- The influence vector unfolds to the derivative of the map at the cell mean. -/
example (w : (Fin 3 × Fin 2) × Fin 3) :
    influence (indepCauseLaw pTJ pC) 1 w =
      fderiv ℝ (ajMap 1) (cellMean (indepCauseLaw pTJ pC)) (cellVector w) := rfl

end Canonical

end MathlibExtTest.Probability.Statistics.AalenJohansenCLT
