/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.IntervalCensoringIdentification
public import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory
open MathlibExt.Probability.Statistics.Censoring MathlibExt.Probability.Statistics.IntervalCensoring

namespace MathlibExtTest.Probability.Statistics.IntervalCensoringIdentification

/-! Case II interval censoring on the grid `Fin 4` with fixed inspection times `1` and `2`. The
facts below are computed from the definitions, not from the theorems under test. -/

/-- Inspect at times `1` and `2` with probability one. -/
noncomputable def pS : PMF (Finset (Fin 4)) := PMF.pure {1, 2}

theorem obs_pure (t : Fin 4) : icObsLaw (PMF.pure t) pS = PMF.pure ({1, 2}, inspect {1, 2} t) := by
  rw [icObsLaw, pS, PMF.pure_bind, inspectLaw, PMF.pure_map, PMF.pure_map]

theorem hazard_pure_self (t : Fin 4) : hazard (PMF.pure t) t = 1 := by
  simp [hazard, survivalMass, PMF.toMeasure_pure, measureReal_def, PMF.pure_apply]

theorem hazard_pure_of_ne {t j : Fin 4} (h : t ≠ j) : hazard (PMF.pure t) j = 0 := by
  simp [hazard, PMF.pure_apply, Ne.symm h]

/-- Boundary conventions of the cell `(L, R]` in the module docstring. An event at `0` precedes
every inspection, so `L = ⊥` (`-∞`) and `R = 1`. -/
example : (({1, 2} : Finset (Fin 4)).filter (· < 0)).max = ⊥ ∧
    (({1, 2} : Finset (Fin 4)).filter (0 ≤ ·)).min = ((1 : Fin 4) : WithTop (Fin 4)) := by
  decide

/-- An event at `3` follows every inspection, so `L = 2` and `R = ⊤` (`+∞`). -/
example : (({1, 2} : Finset (Fin 4)).filter (· < 3)).max = ((2 : Fin 4) : WithBot (Fin 4)) ∧
    (({1, 2} : Finset (Fin 4)).filter (3 ≤ ·)).min = ⊤ := by
  decide

/-- With no inspections (`S = ∅`) nothing is seen, whatever the event time. -/
example (t : Fin 4) : inspect ∅ t = ∅ := Finset.filter_empty _

/-- Grid point `0` is never inspected; `1` and `2` are. -/
theorem zero_notMem : (0 : Fin 4) ∉ inspSupport pS := by
  rintro ⟨S, hS, hc⟩
  rw [pS, PMF.support_pure, Set.mem_singleton_iff] at hS
  subst hS
  exact absurd hc (by decide)

theorem one_mem : (1 : Fin 4) ∈ inspSupport pS :=
  ⟨{1, 2}, by simp [pS], by decide⟩

theorem two_mem : (2 : Fin 4) ∈ inspSupport pS :=
  ⟨{1, 2}, by simp [pS], by decide⟩

/-- Non-identifiability at `1`: events at `0` and at `1` look identical (both are before the first
inspection), yet their hazards at `1` are `0` and `1`. This is the situation of
`exists_hazard_ne_of_prev_notMem`, with `0 ∉ inspSupport pS`. -/
example : icObsLaw (PMF.pure (0 : Fin 4)) pS = icObsLaw (PMF.pure 1) pS ∧
    hazard (PMF.pure (0 : Fin 4)) 1 ≠ hazard (PMF.pure (1 : Fin 4)) 1 := by
  have h01 : inspect {1, 2} (0 : Fin 4) = inspect {1, 2} 1 := by decide
  refine ⟨by rw [obs_pure, obs_pure, h01], ?_⟩
  rw [hazard_pure_of_ne (by decide), hazard_pure_self]
  norm_num

/-- Events at `2` and at `3` are distinguished by the inspection at `2`: their hazards at `2`
(`1` and `0`) differ and so do their observed laws, consistent with `hazard_eq_of_icObsLaw_eq`
at `j = 2`, where `1, 2 ∈ inspSupport pS`. -/
example : icObsLaw (PMF.pure (2 : Fin 4)) pS ≠ icObsLaw (PMF.pure 3) pS ∧
    hazard (PMF.pure (2 : Fin 4)) 2 ≠ hazard (PMF.pure (3 : Fin 4)) 2 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [obs_pure, obs_pure] at h
    have h' := DFunLike.congr_fun h ({1, 2}, inspect {1, 2} 2)
    have hne : (({1, 2}, inspect {1, 2} 2) : Finset (Fin 4) × Finset (Fin 4)) ≠
        ({1, 2}, inspect {1, 2} 3) := by decide
    simp [PMF.pure_apply, hne] at h'
  · rw [hazard_pure_self, hazard_pure_of_ne (by decide)]
    norm_num

/-- The hypotheses of `hazard_eq_of_icObsLaw_eq` hold at `j = 2`. -/
example {pT pT' : PMF (Fin 4)} (h : icObsLaw pT pS = icObsLaw pT' pS) :
    hazard pT 2 = hazard pT' 2 :=
  hazard_eq_of_icObsLaw_eq h (Or.inl two_mem) fun i hi => by
    obtain rfl : i = 1 := Fin.ext (by simpa using hi)
    exact one_mem

/-- The last grid point `3` is never inspected, but `F(3) = 1`, so `hazard_eq_of_icObsLaw_eq`
applies at `3` once `2` is inspected. This is not substantive identification: the hazard at the
last point is `1` whenever `P(T ≥ 3) > 0` and `0` otherwise, by the `x / 0 = 0` convention. -/
example {pT pT' : PMF (Fin 4)} (h : icObsLaw pT pS = icObsLaw pT' pS) :
    hazard pT 3 = hazard pT' 3 :=
  hazard_eq_of_icObsLaw_eq h (Or.inr rfl) fun i hi => by
    obtain rfl : i = 2 := Fin.ext (by simpa using hi)
    exact two_mem

/-- The characterization rules out `j = 1` (because `0` is never inspected). -/
example : ¬ ∀ pT pT' : PMF (Fin 4),
    icObsLaw pT pS = icObsLaw pT' pS → hazard pT 1 = hazard pT' 1 := fun h =>
  zero_notMem ((hazard_identified_iff.1 h).2 0 rfl)

/-! Current status data: a single inspection time with law `pC`. -/

theorem currentStatus_one_mem (pC : PMF (Fin 4)) (h : pC 1 ≠ 0) :
    (1 : Fin 4) ∈ inspSupport (currentStatus pC) :=
  ⟨{1}, by
    rw [currentStatus, PMF.mem_support_iff, PMF.map_apply]
    exact ENNReal.summable.tsum_ne_zero_iff.2 ⟨1, by simpa using h⟩, Finset.mem_singleton_self _⟩

theorem currentStatus_two_mem (pC : PMF (Fin 4)) (h : pC 2 ≠ 0) :
    (2 : Fin 4) ∈ inspSupport (currentStatus pC) :=
  ⟨{2}, by
    rw [currentStatus, PMF.mem_support_iff, PMF.map_apply]
    exact ENNReal.summable.tsum_ne_zero_iff.2 ⟨2, by simpa using h⟩, Finset.mem_singleton_self _⟩

/-- `inspSupport_currentStatus` agrees with the membership computed above. -/
example (pC : PMF (Fin 4)) (h : pC 1 ≠ 0) : (1 : Fin 4) ∈ pC.support := by
  rw [← inspSupport_currentStatus]
  exact currentStatus_one_mem pC h

/-- Current status inspection at `1` or `2` (each with positive probability) identifies the
hazard at `2`. -/
example (pC : PMF (Fin 4)) (h1 : pC 1 ≠ 0) (h2 : pC 2 ≠ 0) {pT pT' : PMF (Fin 4)}
    (h : icObsLaw pT (currentStatus pC) = icObsLaw pT' (currentStatus pC)) :
    hazard pT 2 = hazard pT' 2 :=
  hazard_eq_of_icObsLaw_eq h (Or.inl (currentStatus_two_mem pC h2)) fun i hi => by
    obtain rfl : i = 1 := Fin.ext (by simpa using hi)
    exact currentStatus_one_mem pC h1

end MathlibExtTest.Probability.Statistics.IntervalCensoringIdentification
