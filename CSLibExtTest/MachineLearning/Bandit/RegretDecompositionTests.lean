/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.MachineLearning.Bandit.RegretDecomposition

/-!
# Regret decomposition tests

Checks of the regret decomposition: the grouping of the rounds of an explicit history by arm,
the horizon zero, the nonnegativity of the regret recovered from the decomposition, the zero
regret of every policy when all arms have the same mean, and, on a two-armed bandit with
point-mass rewards `0` and `1`, the regret of every policy equal to the expected number of pulls
of the worse arm, at most the horizon.
-/

namespace CSLibExtTest.MachineLearning.Bandit.RegretDecomposition

open MeasureTheory Finset Cslib.MachineLearning.Bandit

/-! ## Grouping the rounds of a history by arm -/

/-- A history of three rounds with two arms: arm `0`, then arm `1`, then arm `0`. -/
noncomputable def hist : History 2 3 := ![(0, 1), (1, 0), (0, 5)]

/-- Summing `f A_t` over the three rounds gives `f 0 + f 1 + f 0 = 2 f 0 + f 1`. -/
example (f : Fin 2 → ℝ) : ∑ t, f (hist t).1 = 2 * f 0 + f 1 := by
  rw [sum_comp_fst_eq_sum_pullCount_mul, Fin.sum_univ_two,
    show pullCount 0 hist = 2 by decide, show pullCount 1 hist = 1 by decide]
  norm_num

/-- In the empty history, both sides vanish. -/
example {k : ℕ} (f : Fin k → ℝ) (h : History k 0) : ∑ i, (pullCount i h : ℝ) * f i = 0 := by
  rw [← sum_comp_fst_eq_sum_pullCount_mul]
  simp

/-! ## Consequences of the decomposition -/

section Consequences

variable {k : ℕ} [NeZero k] (ν : StochasticBandit k) (hν : ν.HasFiniteMeans) (π : Policy k)
include hν

/-- At horizon zero, every expected pull count vanishes, and so does the regret. -/
example : regret ν π 0 = 0 := by
  rw [regret_eq_sum_sub_mul_integral_pullCount ν π hν]
  simp [fun i (h : History k 0) ↦ Nat.le_zero.1 (pullCount_le i h)]

/-- The decomposition gives the nonnegativity of the regret again: the gaps and the expected
pull counts are nonnegative. -/
example (n : ℕ) : 0 ≤ regret ν π n := by
  rw [regret_eq_sum_sub_mul_integral_pullCount ν π hν]
  exact sum_nonneg fun i _ ↦ mul_nonneg (sub_nonneg.2 (ν.mean_le_maxMean i))
    (integral_nonneg fun _ ↦ Nat.cast_nonneg _)

/-- When all arms have the same mean, every gap vanishes, and so does the regret of every policy
at every horizon. -/
example (c : ℝ) (hc : ∀ i, ν.mean i = c) (n : ℕ) : regret ν π n = 0 := by
  obtain ⟨j, hj⟩ := ν.exists_mean_eq_maxMean
  rw [regret_eq_sum_sub_mul_integral_pullCount ν π hν]
  simp [hc, ← hj]

end Consequences

/-! ## Two arms paying `0` and `1` -/

/-- The bandit whose arm `i` always pays `c i`. -/
noncomputable def diracBandit {k : ℕ} (c : Fin k → ℝ) : StochasticBandit k where
  law i := Measure.dirac (c i)
  isProbabilityMeasure_law _ := inferInstance

theorem diracBandit_hasFiniteMeans {k : ℕ} (c : Fin k → ℝ) : (diracBandit c).HasFiniteMeans :=
  fun _ ↦ integrable_dirac (by simp)

theorem diracBandit_mean {k : ℕ} (c : Fin k → ℝ) (i : Fin k) : (diracBandit c).mean i = c i := by
  simp [StochasticBandit.mean, diracBandit]

theorem maxMean_diracBandit_zero_one : (diracBandit ![0, 1]).maxMean = 1 := by
  refine le_antisymm (sup'_le _ _ fun i _ ↦ ?_) ?_
  · fin_cases i <;> simp [diracBandit_mean]
  · simpa [diracBandit_mean] using (diracBandit ![0, 1]).mean_le_maxMean 1

/-- On the bandit whose arms pay `0` and `1`, the regret of every policy is the expected number of
pulls of the worse arm `0`: its gap is `1` and the better arm's is `0`. -/
theorem regret_diracBandit_zero_one (π : Policy 2) (n : ℕ) :
    regret (diracBandit ![0, 1]) π n =
      ∫ h, (pullCount 0 h : ℝ) ∂canonicalLaw (diracBandit ![0, 1]) π n := by
  rw [regret_eq_sum_sub_mul_integral_pullCount _ π (diracBandit_hasFiniteMeans _),
    Fin.sum_univ_two, maxMean_diracBandit_zero_one]
  simp [diracBandit_mean]

/-- So that regret is at most the horizon `n`. -/
example (π : Policy 2) (n : ℕ) : regret (diracBandit ![0, 1]) π n ≤ n := by
  rw [regret_diracBandit_zero_one]
  calc ∫ h, (pullCount 0 h : ℝ) ∂canonicalLaw (diracBandit ![0, 1]) π n
      ≤ ∫ _h, (n : ℝ) ∂canonicalLaw (diracBandit ![0, 1]) π n :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ Nat.cast_nonneg _) (integrable_const _)
          (ae_of_all _ fun h ↦ (by exact_mod_cast pullCount_le 0 h :
            ((pullCount 0 h : ℕ) : ℝ) ≤ n))
    _ = n := by simp

end CSLibExtTest.MachineLearning.Bandit.RegretDecomposition
