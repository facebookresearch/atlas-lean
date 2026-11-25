/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.CusumOptimality
public import MathlibExtTest.Probability.Statistics.WaldInequalities

/-!
# Tests for Moustakides' theorem

The instance of the tests of Wald's inequalities: observations with values in `Bool`, the fair
coin before the change and the coin with `P {true} = 1/3` after it. The tests compare the CUSUM
alarm with an alarm raised at a fixed time, with an alarm that is never raised (its mean time to
false alarm is infinite) and with CUSUM at a larger threshold, and check that an alarm raised
before any observation is never admissible: its mean time to false alarm is `0`, while that of
CUSUM is at least `1`.
-/

@[expose] public section

open MeasureTheory
open MathlibExtTest.Probability.Statistics.WaldInequalities
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.CusumOptimality

/-- Raising the alarm at a fixed time is a stopping time. -/
theorem isStoppingTime_const_time (n : ℕ) :
    IsStoppingTime (observationFiltration Bool) (fun _ : ℕ → Bool => (n : WithTop ℕ)) :=
  isStoppingTime_const _ n

/-- Never raising the alarm is a stopping time. -/
theorem isStoppingTime_top :
    IsStoppingTime (observationFiltration Bool) (fun _ : ℕ → Bool => (⊤ : WithTop ℕ)) := by
  intro i
  show MeasurableSet[observationFiltration Bool i] {ω : ℕ → Bool | (⊤ : WithTop ℕ) ≤ i}
  have : {ω : ℕ → Bool | (⊤ : WithTop ℕ) ≤ i} = ∅ := by
    ext ω
    simp
  rw [this]
  exact @MeasurableSet.empty _ (observationFiltration Bool i)

/-- The mean of an alarm raised at the fixed time `n` is `n`. -/
theorem lintegral_const_time (n : ℕ) :
    ∫⁻ _, ((show ℕ∞ from ((n : ℕ) : WithTop ℕ)) : ℝ≥0∞)
      ∂Measure.infinitePi (fun _ : ℕ => fairCoin) = n := by
  rw [lintegral_const, measure_univ, mul_one]
  exact ENat.toENNReal_coe n

/-- **CUSUM against a fixed alarm time.** If the alarm raised at the fixed time `n` has a mean time
to false alarm at least that of CUSUM, then the worst-case delay of CUSUM is no greater. -/
example {c : ℝ} (hc : 0 < c) (n : ℕ)
    (hn : ∫⁻ ω, ((show ℕ∞ from cusumTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac c ω) :
      ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => fairCoin) ≤ n) :
    lordenDelay fairCoin biasedCoin (cusumTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac c) ≤
      lordenDelay fairCoin biasedCoin (fun _ => (n : WithTop ℕ)) :=
  cusumTime_lordenDelay_le biasedCoin_ac fairCoin_ac fairCoin_ne_biasedCoin hc rfl
    (isStoppingTime_const_time n) (hn.trans_eq (lintegral_const_time n).symm)

/-- An alarm that is never raised has an infinite mean time to false alarm, so the theorem
applies to it (its worst-case delay is `∞`). -/
example {c : ℝ} (hc : 0 < c) :
    lordenDelay fairCoin biasedCoin (cusumTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac c) ≤
      lordenDelay fairCoin biasedCoin (fun _ => (⊤ : WithTop ℕ)) := by
  refine cusumTime_lordenDelay_le biasedCoin_ac fairCoin_ac fairCoin_ne_biasedCoin hc rfl
    isStoppingTime_top ?_
  have htop : ∫⁻ ω, ((show ℕ∞ from (⊤ : WithTop ℕ)) : ℝ≥0∞)
      ∂Measure.infinitePi (fun _ : ℕ => fairCoin) = ∞ := by
    rw [lintegral_const, measure_univ, mul_one]
    exact ENat.toENNReal_top
  rw [htop]
  exact le_top

/-- **Raising the threshold does not speed up CUSUM.** A threshold `c' ≥ c` gives an alarm no
earlier, hence a mean time to false alarm no smaller, so the theorem compares the two CUSUM alarms:
the worst-case delay of CUSUM does not decrease as its threshold increases. -/
example {c c' : ℝ} (hc : 0 < c) (hcc' : c ≤ c') :
    lordenDelay fairCoin biasedCoin (cusumTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac c) ≤
      lordenDelay fairCoin biasedCoin
        (cusumTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac c') := by
  refine cusumTime_lordenDelay_le biasedCoin_ac fairCoin_ac fairCoin_ne_biasedCoin hc rfl
    (isStoppingTime_cusumTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac c')
    (lintegral_mono fun ω => ENat.toENNReal_mono ?_)
  exact hittingAfter_apply_anti (pageCusum fairCoin biasedCoin biasedCoin_ac fairCoin_ac) 1 ω
    (Set.Ici_subset_Ici.2 hcc')

/-- **Edge case: alarm before any observation.** CUSUM never stops before the first observation,
so its mean time to false alarm is at least `1`; the alarm raised at time `0`, whose mean time to
false alarm is `0`, therefore never satisfies the constraint of the theorem. -/
example (c : ℝ) :
    ∫⁻ _, ((show ℕ∞ from ((0 : ℕ) : WithTop ℕ)) : ℝ≥0∞)
        ∂Measure.infinitePi (fun _ : ℕ => fairCoin) <
      ∫⁻ ω, ((show ℕ∞ from cusumTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac c ω) : ℝ≥0∞)
        ∂Measure.infinitePi (fun _ : ℕ => fairCoin) := by
  rw [lintegral_const_time, Nat.cast_zero]
  calc (0 : ℝ≥0∞) < 1 := zero_lt_one
    _ = ∫⁻ _, 1 ∂Measure.infinitePi (fun _ : ℕ => fairCoin) := by simp
    _ ≤ _ := lintegral_mono fun ω => by
        have h := le_hittingAfter
          (u := pageCusum fairCoin biasedCoin biasedCoin_ac fairCoin_ac) (s := Set.Ici c)
          (n := 1) ω
        refine le_trans ?_ (ENat.toENNReal_mono h)
        show (1 : ℝ≥0∞) ≤ ((1 : ℕ∞) : ℝ≥0∞)
        simp

end MathlibExtTest.Probability.Statistics.CusumOptimality
