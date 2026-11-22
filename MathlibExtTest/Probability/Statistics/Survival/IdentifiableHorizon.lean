/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.IdentifiableHorizon
public import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory Finset
open MathlibExt.Probability.Statistics.KaplanMeier MathlibExt.Probability.Statistics.Censoring

namespace MathlibExtTest.Probability.Statistics.IdentifiableHorizon

/-! ### Sample level: the residual location of the Kaplan–Meier NPMLE -/

/-- Two subjects observed at time `0`: one death and one censoring. The censored subject is at
the last observation time, so half of the Kaplan–Meier mass is left over. -/
def Dcens : CensoredData 1 where
  time := fun _ => 0
  strictMono_time := fun i j h => absurd h (by omega)
  deaths := fun _ => 1
  censored := fun _ => 1

theorem Dcens_kmTail_pos : 0 < Dcens.kmTail :=
  Dcens.kmTail_pos_of_censored_pos (j := 0) (fun _ => le_rfl) (by decide)

/-- Non-vacuity of `kmMeasure_tail_not_identified`: placing the residual mass at `1` or at `2`
gives two different NPMLEs that agree on `(-∞, 0]`. -/
example : Dcens.kmMeasure 1 ≠ Dcens.kmMeasure 2 ∧
    (Dcens.kmMeasure 1).restrict (Set.Iic 0) = (Dcens.kmMeasure 2).restrict (Set.Iic 0) ∧
    Dcens.likelihood (Dcens.kmMeasure 1) = Dcens.likelihood (Dcens.kmMeasure 2) ∧
    ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      Dcens.likelihood ν ≤ Dcens.likelihood (Dcens.kmMeasure 1) ∧
        Dcens.likelihood ν ≤ Dcens.likelihood (Dcens.kmMeasure 2) :=
  Dcens.kmMeasure_tail_not_identified (s := 0) (fun _ => le_rfl) Dcens_kmTail_pos.ne'
    (by norm_num) (by norm_num) (by norm_num)

example : Dcens.likelihood (Dcens.kmMeasure 1) = Dcens.likelihood (Dcens.kmMeasure 2) :=
  have := Dcens.kmMeasure_isProbabilityMeasure 1
  have := Dcens.kmMeasure_isProbabilityMeasure 2
  Dcens.likelihood_eq_of_restrict_Iic_eq (s := 0) (fun _ => le_rfl)
    (Dcens.kmMeasure_restrict_Iic_eq (by norm_num) (by norm_num))

example : Dcens.kmMeasure 1 ≠ Dcens.kmMeasure 2 :=
  Dcens.kmMeasure_ne_of_kmTail_ne_zero Dcens_kmTail_pos.ne' (fun _ => by norm_num [Dcens])
    (by norm_num)

example : Dcens.kmSurvival 5 = Dcens.kmTail :=
  Dcens.kmSurvival_eq_kmTail fun _ => by norm_num [Dcens]

/-- Any law agreeing with the Kaplan–Meier measure up to the horizon is an NPMLE. -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : μ.restrict (Set.Iic 0) = (Dcens.kmMeasure 1).restrict (Set.Iic 0))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] : Dcens.likelihood ν ≤ Dcens.likelihood μ :=
  Dcens.likelihood_le_of_restrict_Iic_eq_kmMeasure (s := 0) (fun _ => le_rfl) zero_lt_one h ν

/-- One subject observed to die at time `0`: no residual mass. -/
def Ddeath : CensoredData 1 where
  time := fun _ => 0
  strictMono_time := fun i j h => absurd h (by omega)
  deaths := fun _ => 1
  censored := fun _ => 0

theorem Ddeath_kmTail : Ddeath.kmTail = 0 := by
  simp [CensoredData.kmTail, CensoredData.kmFactor, CensoredData.atRisk, Ddeath]

/-- Without residual mass the location is irrelevant. -/
example : Ddeath.kmMeasure 1 = Ddeath.kmMeasure 2 :=
  Ddeath.kmMeasure_eq_of_kmTail_eq_zero Ddeath_kmTail 1 2

/-! ### Population level: the observed-data law and the censoring horizon -/

/-- Censoring at `0` with probability one: the horizon is `0`. -/
theorem isCensoringHorizon_pure_zero : IsCensoringHorizon (PMF.pure (0 : Fin 3)) 0 := by
  refine ⟨by simp, fun c hc => ?_⟩
  simp [PMF.pure_apply, hc.ne']

/-- Non-vacuity of `censoredObsLaw_indepLaw_eq_of_eqOn_Iic`: `T = 1` and `T = 2` are different laws
beyond the horizon `0`, with the same observed-data law. -/
example : PMF.pure (1 : Fin 3) ≠ PMF.pure 2 ∧
    censoredObsLaw (indepLaw (PMF.pure (1 : Fin 3)) (PMF.pure 0)) =
      censoredObsLaw (indepLaw (PMF.pure 2) (PMF.pure 0)) := by
  refine ⟨fun h => ?_,
    (censoredObsLaw_indepLaw_eq_iff isCensoringHorizon_pure_zero).2 fun t ht => ?_⟩
  · have := congrArg (fun p : PMF (Fin 3) => p 1) h
    simp [PMF.pure_apply] at this
  · have ht0 : t = 0 := le_antisymm ht (Fin.zero_le t)
    subst ht0
    simp [PMF.pure_apply]

/-- Censoring at `1` with probability one: the horizon is `1`. -/
theorem isCensoringHorizon_pure_one : IsCensoringHorizon (PMF.pure (1 : Fin 3)) 1 := by
  refine ⟨by simp, fun c hc => ?_⟩
  simp [PMF.pure_apply, hc.ne']

/-- Identification up to the horizon: `T = 0` and `T = 1` differ at `0 ≤ 1`, so their observed
laws differ. -/
example : censoredObsLaw (indepLaw (PMF.pure (0 : Fin 3)) (PMF.pure 1)) ≠
    censoredObsLaw (indepLaw (PMF.pure 1) (PMF.pure 1)) := by
  intro h
  have := eqOn_Iic_of_censoredObsLaw_indepLaw_eq isCensoringHorizon_pure_one.1 h 0 (Fin.zero_le _)
  simp [PMF.pure_apply] at this

example {h' : Fin 3} (hh : IsCensoringHorizon (PMF.pure (0 : Fin 3)) h') : h' = 0 :=
  hh.unique isCensoringHorizon_pure_zero

/-- The observed masses of `Censoring` are read off the observed-data law. -/
example (μ : Measure (Fin 3 × Fin 3)) (j : Fin 3) :
    obsEventMass μ j = (censoredObsLaw μ).real {(j, true)} ∧
      obsAtRiskMass μ j = (censoredObsLaw μ).real {x | j ≤ x.1} :=
  ⟨obsEventMass_eq_censoredObsLaw μ j, obsAtRiskMass_eq_censoredObsLaw μ j⟩

example : censoredObsMap ((1 : Fin 3), (2 : Fin 3)) = (1, true) := by decide

example : censoredObsMap ((2 : Fin 3), (1 : Fin 3)) = (1, false) := by decide

example (pT pC : PMF (Fin 3)) (j : Fin 3) :
    censoredObsLaw (indepLaw pT pC) {(j, false)} = pT.toMeasure {t | j < t} * pC j :=
  censoredObsLaw_indepLaw_false pT pC j

end MathlibExtTest.Probability.Statistics.IdentifiableHorizon
