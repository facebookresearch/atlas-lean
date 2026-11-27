/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.SynchronizerObservationBudget
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PhyslibExt.Electronics.LogicObservationBands
open PhyslibExt.Electronics.SynchronizerObservationBudget

namespace PhyslibExtTest.Electronics.SynchronizerObservationBudget

/-- A mid-band voltage is invalid: `observe 1 2 (3 / 2) = none`. -/
example : observe 1 2 (3 / 2 : ℝ) = none :=
  invalidObservation_one_two_three_halves

example : invalidObservation 1 2 (3 / 2 : ℝ) :=
  invalidObservation_one_two_three_halves

/-- Valid-band voltages: a low voltage at `1 / 2` and a high voltage
at `3`, for thresholds `1` and `2`. -/
example : observe 1 2 (1 / 2 : ℝ) = some false :=
  observe_eq_false_of_le (by norm_num) _
example : observe 1 2 (3 : ℝ) = some true :=
  observe_eq_true_of_le (by norm_num) (by norm_num)

/-- Noise-shifted valid values: a promised low output at `0` shifted
by `1 / 2`, and a promised high output at `3` shifted by `1 / 4`,
both below the unit noise margins for `Vol = 0` and `Voh = 3`. -/
example : observe 1 2 ((0 : ℝ) + 1 / 2) = some false :=
  observe_noisy_low (Vol := 0) (y := 0) (e := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
example : observe 1 2 ((3 : ℝ) + 1 / 4) = some true :=
  observe_noisy_high (Voh := 3) (y := 3) (e := 1 / 4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Within budget, a concrete settling model with expected bit
`false`, ideal voltage `0`, noise `1 / 4` and observed voltage
`1 / 4` is observed as `false`. -/
example :
    observe 1 2 ((fun _ : Fin 1 => fun _ : Unit => (1 / 4 : ℝ)) 0 ()) = some false := by
  have hmodel : settlingGuarantee 1 2 0 3
      (fun _ : Fin 1 => fun _ : Unit => (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ))
      (fun _ : Fin 1 => fun _ : Unit => (0 : ℝ))
      (fun _ : Fin 1 => fun _ : Unit => (1 / 4 : ℝ))
      (fun _ : Fin 1 => fun _ : Unit => (1 / 4 : ℝ))
      (fun _ : Fin 1 => fun _ : Unit => false) := by
    refine ⟨fun _ _ => by norm_num, fun _ _ _ => Or.inl ⟨rfl, le_refl 0⟩, fun _ _ _ => ?_⟩
    norm_num
  have h := observe_observedVoltage_eq_some_of_le 1 2 0 3 (by norm_num) (by norm_num)
    (by norm_num) (fun _ : Fin 1 => fun _ : Unit => (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ))
    (fun _ : Fin 1 => fun _ : Unit => (0 : ℝ))
    (fun _ : Fin 1 => fun _ : Unit => (1 / 4 : ℝ))
    (fun _ : Fin 1 => fun _ : Unit => (1 / 4 : ℝ))
    (fun _ : Fin 1 => fun _ : Unit => false) hmodel 0 () (by norm_num)
  exact h

/-- The two-observation equal-budget sum over `Fin 2`:
`sum (Fin 2) (c * exp (-b / tau)) = 2 * (c * exp (-b / tau))`. -/
example (c b tau : ℝ) :
    ∑ _i : Fin 2, (c * Real.exp (-b / tau)) = 2 * (c * Real.exp (-b / tau)) := by
  rw [Fin.sum_univ_two]
  ring

/-! ### API-level checks on a two-observation model

The sample space is `Unit` with the point mass. Observation `0` has
resolution time `2` past its budget `0` and reads the mid-band
voltage `3 / 2`; observation `1` resolves at time `0` and reads the
low output `0`. Every within-budget clause holds, observation `0` is
invalid, and the capped union bound with `c = 1` evaluates to
`min 1 2 = 1`, which the point mass attains. -/

/-- Resolution times of the two-observation model. -/
noncomputable def twoTime : Fin 2 → Unit → ℝ := fun i _ => ![2, 0] i

/-- Budgets of the two-observation model. -/
noncomputable def twoBudget : Fin 2 → ℝ := fun _ => 0

/-- Ideal voltages of the two-observation model. -/
noncomputable def twoIdeal : Fin 2 → Unit → ℝ := fun i _ => ![3 / 2, 0] i

/-- Noise of the two-observation model. -/
noncomputable def twoNoise : Fin 2 → Unit → ℝ := fun _ _ => 0

/-- Expected bits of the two-observation model. -/
def twoBit : Fin 2 → Unit → Bool := fun _ _ => false

lemma two_settlingGuarantee :
    settlingGuarantee 1 2 0 3 twoTime twoBudget twoIdeal twoNoise twoIdeal twoBit := by
  refine ⟨fun _ _ => by simp [twoNoise], fun i _ h => ?_, fun _ _ _ => ?_⟩
  · fin_cases i
    · norm_num [twoTime, twoBudget] at h
    · exact Or.inl ⟨rfl, by simp [twoIdeal]⟩
  · norm_num [twoNoise]

lemma two_invalid_zero : invalidObservation 1 2 (twoIdeal 0 ()) := by
  simpa [twoIdeal] using invalidObservation_one_two_three_halves

lemma two_measurableSet (i : Fin 2) :
    MeasurableSet (invalidEvent 1 2 twoIdeal i) :=
  (Set.toFinite _).measurableSet

lemma two_tail (i : Fin 2) :
    Measure.dirac () (resolutionExceedsEvent twoTime twoBudget i) ≤
      ENNReal.ofReal (1 * Real.exp (-twoBudget i / 1)) := by
  have h : Measure.dirac () (resolutionExceedsEvent twoTime twoBudget i) ≤ 1 := prob_le_one
  simpa [twoBudget] using h

/-- Invalid implies expiry on the concrete model: observation `0` is
invalid, so its budget `0` is below its resolution time `2`. -/
example : twoBudget 0 < twoTime 0 () :=
  resolutionExceeds_of_invalidObservation 1 2 0 3 (by norm_num) (by norm_num)
    (by norm_num) twoTime twoBudget twoIdeal twoNoise twoIdeal twoBit
    two_settlingGuarantee 0 () two_invalid_zero

/-- Event form of the inclusion on the concrete model. -/
example : invalidEvent 1 2 twoIdeal 0 ⊆ resolutionExceedsEvent twoTime twoBudget 0 :=
  invalidEvent_subset_resolutionExceedsEvent 1 2 0 3 (by norm_num) (by norm_num)
    (by norm_num) twoTime twoBudget twoIdeal twoNoise twoIdeal twoBit
    two_settlingGuarantee 0

/-- Tail transfer on the concrete model. -/
example :
    Measure.dirac () (invalidEvent 1 2 twoIdeal 0) ≤
      ENNReal.ofReal (1 * Real.exp (-twoBudget 0 / 1)) :=
  measure_invalidEvent_le_of_tail (Measure.dirac ()) 1 2 0 3 (by norm_num)
    (by norm_num) (by norm_num) twoTime twoBudget twoIdeal twoNoise twoIdeal twoBit
    two_settlingGuarantee 1 1 0 (two_tail 0)

/-- The uncapped union bound over `Fin 2` evaluates to `2`. -/
example : Measure.dirac () (⋃ i : Fin 2, invalidEvent 1 2 twoIdeal i) ≤ 2 := by
  have h := measure_biUnion_invalidEvent_le_sum (Measure.dirac ()) 1 2 0 3
    (by norm_num) (by norm_num) (by norm_num) twoTime twoBudget twoIdeal twoNoise
    twoIdeal twoBit two_settlingGuarantee two_measurableSet 1 1 (by norm_num)
    (by norm_num) (fun _ => le_refl 0) two_tail
  simpa [twoBudget, Fin.sum_univ_two, one_add_one_eq_two] using h

/-- The equal-budget form over `Fin 2`: the cardinality coercion gives
`min 1 (2 * 1)`. -/
example :
    Measure.dirac () (⋃ i : Fin 2, invalidEvent 1 2 twoIdeal i) ≤
      min 1 ((2 : ℝ≥0∞) * 1) := by
  have h := measure_biUnion_invalidEvent_le_min_one_card_mul (Measure.dirac ())
    1 2 0 3 (by norm_num) (by norm_num) (by norm_num) twoTime twoBudget twoIdeal
    twoNoise twoIdeal twoBit two_settlingGuarantee two_measurableSet 1 1 0
    (by norm_num) (by norm_num) le_rfl (fun _ => rfl) two_tail
  simpa using h

/-- The headline bound over `Fin 2`, and the point mass attains the cap:
the event of any invalid observation has probability one. -/
example :
    Measure.dirac () (⋃ i : Fin 2, invalidEvent 1 2 twoIdeal i) ≤
        min 1 (∑ i : Fin 2, ENNReal.ofReal (1 * Real.exp (-twoBudget i / 1))) ∧
      Measure.dirac () (⋃ i : Fin 2, invalidEvent 1 2 twoIdeal i) = 1 := by
  refine ⟨anyInvalid_measure_le_min_one_sum (Measure.dirac ()) 1 2 0 3
    (by norm_num) (by norm_num) (by norm_num) twoTime twoBudget twoIdeal twoNoise twoIdeal
    twoBit two_settlingGuarantee two_measurableSet 1 1 (by norm_num) (by norm_num)
    (fun _ => le_refl 0) two_tail, ?_⟩
  exact Measure.dirac_apply_of_mem (Set.mem_iUnion.mpr ⟨0, two_invalid_zero⟩)

/-- The empty index: no observations give probability zero, and the
equal-budget bound collapses to `min 1 0 = 0`. -/
example (Vil Vih : ℝ) (v : Fin 0 → Unit → ℝ) :
    Measure.dirac () (⋃ i : Fin 0, invalidEvent Vil Vih v i) = 0 :=
  measure_biUnion_invalidEvent_eq_zero_of_isEmpty (Measure.dirac ()) Vil Vih v

example (c tau b : ℝ) (hc : 0 ≤ c) (htau : 0 < tau) (hb : 0 ≤ b)
    (t : Fin 0 → Unit → ℝ) (y e v : Fin 0 → Unit → ℝ) (bit : Fin 0 → Unit → Bool) :
    Measure.dirac () (⋃ i : Fin 0, invalidEvent 1 2 v i) ≤
      min 1 ((Fintype.card (Fin 0) : ℝ≥0∞) * ENNReal.ofReal (c * Real.exp (-b / tau))) :=
  measure_biUnion_invalidEvent_le_min_one_card_mul (Measure.dirac ()) 1 2 0 3
    (by norm_num) (by norm_num) (by norm_num) t (fun _ => b) y e v bit
    ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩ (fun i => i.elim0)
    c tau b hc htau hb (fun _ => rfl) (fun i => i.elim0)

end PhyslibExtTest.Electronics.SynchronizerObservationBudget
