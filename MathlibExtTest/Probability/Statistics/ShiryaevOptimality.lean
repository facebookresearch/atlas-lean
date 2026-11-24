/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ShiryaevOptimality
public import MathlibExtTest.Probability.Statistics.WaldInequalities

/-!
# Tests for Shiryaev's theorem

The instance of the tests of Wald's inequalities: observations with values in `Bool`, the fair
coin before the change and the coin with `P {true} = 1/3` after it. The tests compare the
Shiryaev rule with alarms raised at a fixed time and with an alarm that is never raised, and check
that an alarm raised before any observation is never admissible: its false-alarm probability is
`1`, while that of the Shiryaev rule is at most `1 - ρ`.
-/

@[expose] public section

open MeasureTheory
open MathlibExtTest.Probability.Statistics.WaldInequalities
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.ShiryaevOptimality

/-- The Kullback–Leibler divergence of the two coins is finite. -/
theorem klDiv_biasedCoin_fairCoin_ne_top :
    InformationTheory.klDiv biasedCoin fairCoin ≠ ∞ :=
  InformationTheory.klDiv_ne_top biasedCoin_ac (Integrable.of_finite)

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

/-- **The Shiryaev rule against a fixed alarm time.** If raising the alarm at the fixed time `n`
has false-alarm probability at most that of the Shiryaev rule, then the Shiryaev rule has no
greater average detection delay. -/
example {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) {A : ℝ} (hA₀ : 0 < A) (hA₁ : A < 1) (n : ℕ)
    (hn : falseAlarmProb fairCoin biasedCoin ρ hρ₀ hρ₁.le (fun _ => (n : WithTop ℕ)) ≤
      falseAlarmProb fairCoin biasedCoin ρ hρ₀ hρ₁.le
        (shiryaevTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac ρ hρ₀ hρ₁.le A)) :
    averageDetectionDelay fairCoin biasedCoin ρ hρ₀ hρ₁.le
        (shiryaevTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac ρ hρ₀ hρ₁.le A) ≤
      averageDetectionDelay fairCoin biasedCoin ρ hρ₀ hρ₁.le (fun _ => (n : WithTop ℕ)) :=
  shiryaevTime_optimal biasedCoin_ac fairCoin_ac fairCoin_ne_biasedCoin
    klDiv_biasedCoin_fairCoin_ne_top hρ₀ hρ₁ hA₀ hA₁ rfl (isStoppingTime_const_time n) hn

/-- An alarm that is never raised has false-alarm probability `0`, so the theorem applies to it
(its average detection delay is `∞`). -/
example {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) {A : ℝ} (hA₀ : 0 < A) (hA₁ : A < 1) :
    averageDetectionDelay fairCoin biasedCoin ρ hρ₀ hρ₁.le
        (shiryaevTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac ρ hρ₀ hρ₁.le A) ≤
      averageDetectionDelay fairCoin biasedCoin ρ hρ₀ hρ₁.le (fun _ => (⊤ : WithTop ℕ)) := by
  refine shiryaevTime_optimal biasedCoin_ac fairCoin_ac fairCoin_ne_biasedCoin
    klDiv_biasedCoin_fairCoin_ne_top hρ₀ hρ₁ hA₀ hA₁ rfl isStoppingTime_top ?_
  have h0 : falseAlarmProb fairCoin biasedCoin ρ hρ₀ hρ₁.le (fun _ => (⊤ : WithTop ℕ)) = 0 := by
    simp [falseAlarmProb]
  rw [h0]
  exact zero_le

/-- An alarm raised before any observation is a false alarm for every change point: its
false-alarm probability is `1`, the total mass of the geometric prior. -/
theorem falseAlarmProb_zero {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    falseAlarmProb fairCoin biasedCoin ρ hρ₀ hρ₁.le (fun _ => ((0 : ℕ) : WithTop ℕ)) = 1 := by
  have h1 : 0 ≤ 1 - ρ := by linarith
  have hset : ∀ n : ℕ, {ω : ℕ → Bool | ((0 : ℕ) : WithTop ℕ) < ((n + 1 : ℕ) : WithTop ℕ)} =
      Set.univ := fun n => by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact_mod_cast Nat.succ_pos n
  have hP : ∀ n : ℕ, changePointLaw fairCoin biasedCoin (n + 1) Set.univ = 1 := fun n => by
    unfold changePointLaw
    exact measure_univ
  simp only [falseAlarmProb, hset, hP, mul_one]
  have hterm : ∀ n : ℕ, ENNReal.ofReal (ρ * (1 - ρ) ^ n) =
      ENNReal.ofReal ρ * ENNReal.ofReal (1 - ρ) ^ n := fun n => by
    rw [ENNReal.ofReal_mul hρ₀.le, ENNReal.ofReal_pow h1]
  have hsub : 1 - ENNReal.ofReal (1 - ρ) = ENNReal.ofReal ρ := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h1, sub_sub_cancel]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, hsub,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hρ₀).ne' ENNReal.ofReal_ne_top]

/-- A rule that never raises the alarm before the first observation has false-alarm probability at
most `1 - ρ`: the change point `Γ = 1`, of prior mass `ρ`, is never preceded by a false alarm. -/
theorem falseAlarmProb_le_of_one_le {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1)
    {τ : (ℕ → Bool) → WithTop ℕ} (hτ : ∀ ω, (1 : WithTop ℕ) ≤ τ ω) :
    falseAlarmProb fairCoin biasedCoin ρ hρ₀ hρ₁.le τ ≤ ENNReal.ofReal (1 - ρ) := by
  have h1 : 0 ≤ 1 - ρ := by linarith
  unfold falseAlarmProb
  rw [tsum_eq_zero_add' CompleteLattice.summable]
  have h0 : {ω | τ ω < ((0 + 1 : ℕ) : WithTop ℕ)} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact_mod_cast hτ ω
  rw [h0, measure_empty, mul_zero, zero_add]
  calc ∑' n : ℕ, ENNReal.ofReal (ρ * (1 - ρ) ^ (n + 1)) *
          changePointLaw fairCoin biasedCoin (n + 1 + 1)
            {ω | τ ω < ((n + 1 + 1 : ℕ) : WithTop ℕ)}
      ≤ ∑' n : ℕ, ENNReal.ofReal (1 - ρ) * (ENNReal.ofReal ρ * ENNReal.ofReal (1 - ρ) ^ n) := by
        refine tsum_le_tsum fun n => ?_
        calc _ ≤ ENNReal.ofReal (ρ * (1 - ρ) ^ (n + 1)) * 1 := by
              gcongr
              unfold changePointLaw
              exact prob_le_one
          _ = _ := by
              rw [mul_one, ← ENNReal.ofReal_pow h1, ← ENNReal.ofReal_mul hρ₀.le,
                ← ENNReal.ofReal_mul h1]
              congr 1
              ring
    _ = ENNReal.ofReal (1 - ρ) := by
        have hsub : 1 - ENNReal.ofReal (1 - ρ) = ENNReal.ofReal ρ := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h1, sub_sub_cancel]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, hsub,
          ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hρ₀).ne' ENNReal.ofReal_ne_top, mul_one]

/-- **Edge case: alarm before any observation.** The Shiryaev rule never stops before the first
observation, so its false-alarm probability is at most `1 - ρ < 1`; the alarm raised at time `0`,
whose false-alarm probability is `1`, therefore never satisfies the constraint of the theorem. -/
example {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) (A : ℝ) :
    falseAlarmProb fairCoin biasedCoin ρ hρ₀ hρ₁.le
        (shiryaevTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac ρ hρ₀ hρ₁.le A) <
      falseAlarmProb fairCoin biasedCoin ρ hρ₀ hρ₁.le (fun _ => ((0 : ℕ) : WithTop ℕ)) := by
  rw [falseAlarmProb_zero hρ₀ hρ₁]
  refine (falseAlarmProb_le_of_one_le hρ₀ hρ₁ fun ω => le_hittingAfter ω).trans_lt ?_
  rw [← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)

end MathlibExtTest.Probability.Statistics.ShiryaevOptimality
