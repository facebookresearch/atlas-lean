/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CountingProcess

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

namespace MathlibExtTest.Probability.Statistics.CountingProcess

variable {Ω : Type*} [MeasurableSpace Ω] (ω : Ω)

/-! ### Paths of one subject: failure at `T = 2`, censoring at `C = 3` -/

example : obsTime (fun _ : Ω => (2 : ℝ)) (fun _ => 3) ω = 2 := by norm_num [obsTime]

/-- Before the failure, `N = 0`. -/
example : countingProcess (fun _ : Ω => (2 : ℝ)) (fun _ => 3) 1 ω = 0 := by
  norm_num [countingProcess]

/-- At the failure time itself `N` has jumped (right-continuity). -/
example : countingProcess (fun _ : Ω => (2 : ℝ)) (fun _ => 3) 2 ω = 1 := by
  norm_num [countingProcess]

/-- The subject is still at risk at its exit time (left-continuity of `Y`)... -/
example : atRiskProcess (fun _ : Ω => (2 : ℝ)) (fun _ => 3) 2 ω = 1 := by
  norm_num [atRiskProcess]

/-- ...and not after it. -/
example : atRiskProcess (fun _ : Ω => (2 : ℝ)) (fun _ => 3) (5 / 2) ω = 0 := by
  norm_num [atRiskProcess]

/-- An observed failure: the observed process at `t = 5` is `(N, Nᶜ) = (1, 0)`. -/
example : observedProcess (fun _ : Ω => (2 : ℝ)) (fun _ => 3) 5 ω = (1, 0) := by
  norm_num [observedProcess, countingProcess, censoringProcess]

/-! ### A censored subject (`T = 3`, `C = 2`) and a tie (`T = C = 2`) -/

example : countingProcess (fun _ : Ω => (3 : ℝ)) (fun _ => 2) 5 ω = 0 := by
  norm_num [countingProcess]

example : censoringProcess (fun _ : Ω => (3 : ℝ)) (fun _ => 2) 2 ω = 1 := by
  norm_num [censoringProcess]

/-- Ties count as failures, not as censorings. -/
example : countingProcess (fun _ : Ω => (2 : ℝ)) (fun _ => 2) 2 ω = 1 ∧
    censoringProcess (fun _ : Ω => (2 : ℝ)) (fun _ => 2) 2 ω = 0 := by
  norm_num [countingProcess, censoringProcess]

/-- Exactly one exit: `N(t) + Nᶜ(t) = 1{X ≤ t}`. -/
example (T C : Ω → ℝ) (t : ℝ) :
    countingProcess T C t ω + censoringProcess T C t ω = if obsTime T C ω ≤ t then 1 else 0 :=
  countingProcess_add_censoringProcess t ω

/-! ### Hazard measure and compensator -/

/-- **Terminal atom**: for a point mass the hazard measure puts mass `F{1} / F[1, ∞) = 1` at `1`. -/
example : hazardMeasure (Measure.dirac (1 : ℝ)) {1} = 1 := by
  rw [hazardMeasure, withDensity_apply _ (measurableSet_singleton 1), Measure.restrict_singleton,
    lintegral_smul_measure, lintegral_dirac]
  simp

/-- The tail `F[s, ∞)` is almost surely positive, here for a point mass. -/
example : ∀ᵐ s ∂(Measure.dirac (1 : ℝ)), Measure.dirac (1 : ℝ) (Ici s) ≠ 0 :=
  ae_measure_Ici_ne_zero _

/-- The compensator stops at the exit time: `A(5) = Λ((-∞, 2])` for `X = 2`. -/
example : compensator (fun _ : Ω => (2 : ℝ)) (fun _ => 3) (Measure.dirac 1) 5 ω = 1 := by
  rw [compensator_eq]
  norm_num [obsTime]

/-- With `Λ = δ₁` and failure at `2`, the compensated process at `5` is `1 - 1 = 0`. -/
example : compensatedProcess (fun _ : Ω => (2 : ℝ)) (fun _ => 3) (Measure.dirac 1) 5 ω = 0 := by
  rw [compensatedProcess, compensator_eq]
  norm_num [obsTime, countingProcess]

/-! ### The model is non-vacuous: independent coordinates on a product space -/

/-- On `ℝ × ℝ` with a product law, the coordinates are independent. -/
theorem indepFun_fst_snd (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd (P.prod Q) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable, Measure.map_fst_prod, Measure.map_snd_prod]
  simp

/-- The compensated counting process of a product-law subject is a martingale. -/
example (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    Martingale (compensatedProcess Prod.fst Prod.snd (hazardMeasure ((P.prod Q).map Prod.fst)))
      (historyFiltration measurable_fst measurable_snd) (P.prod Q) :=
  martingale_compensatedProcess measurable_fst measurable_snd (indepFun_fst_snd P Q)

/-- Mean identity on the same model: `E N(t) = E A(t)`. -/
example (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (t : ℝ) :
    ∫ p, countingProcess Prod.fst Prod.snd t p ∂(P.prod Q) =
      ∫ p, compensator Prod.fst Prod.snd (hazardMeasure ((P.prod Q).map Prod.fst)) t p
        ∂(P.prod Q) :=
  integral_countingProcess_eq_integral_compensator measurable_fst measurable_snd
    (indepFun_fst_snd P Q) t

/-- `Y(t)` is known strictly before `t`. -/
example (t : ℝ) :
    Measurable[⨆ s < t, historyFiltration (Ω := ℝ × ℝ) measurable_fst measurable_snd s]
      (atRiskProcess Prod.fst Prod.snd t) :=
  measurable_atRiskProcess_strictPast measurable_fst measurable_snd t

/-! ### Several subjects -/

/-- Two subjects, one failing at `2` and one censored at `2`: one failure observed by `5`. -/
example : totalCountingProcess (fun i : Fin 2 => fun _ : Ω => if i = 0 then (2 : ℝ) else 3)
    (fun _ _ => 2) 5 ω = 1 := by
  rw [totalCountingProcess, Fin.sum_univ_two]
  norm_num [countingProcess]

/-- Both subjects are at risk at time `2`, nobody after. -/
example : totalAtRiskProcess (fun i : Fin 2 => fun _ : Ω => if i = 0 then (2 : ℝ) else 3)
    (fun _ _ => 2) 2 ω = 2 ∧
    totalAtRiskProcess (fun i : Fin 2 => fun _ : Ω => if i = 0 then (2 : ℝ) else 3)
    (fun _ _ => 2) 3 ω = 0 := by
  constructor <;> rw [totalAtRiskProcess, Fin.sum_univ_two] <;> norm_num [atRiskProcess]

/-- The aggregated compensated process of an independent cohort is a martingale for the joint
history. -/
example {μ : Measure Ω} [IsProbabilityMeasure μ] (Ts Cs : Fin 3 → Ω → ℝ)
    (hT : ∀ i, Measurable (Ts i)) (hC : ∀ i, Measurable (Cs i))
    (hpair : iIndepFun (fun i ω => (Ts i ω, Cs i ω)) μ) (hind : ∀ i, IndepFun (Ts i) (Cs i) μ) :
    Martingale (fun t ω => totalCountingProcess Ts Cs t ω - totalCompensator μ Ts Cs t ω)
      (jointHistoryFiltration hT hC) μ :=
  martingale_totalCountingProcess_sub_totalCompensator hT hC hpair hind

end MathlibExtTest.Probability.Statistics.CountingProcess
