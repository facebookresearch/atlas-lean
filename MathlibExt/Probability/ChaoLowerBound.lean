/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Chao's lower bound for the number of classes

For a finite list of Poisson rates, the class probabilities for zero, one, and two
observations give the three sums in a weighted Cauchy–Schwarz inequality.

This is the exact expected-count inequality derived from the Poisson model, rather
than a transcription of the original paper. The multinomial model and the plug-in
estimator formed from observed counts are not formalized here.

Source: A. Chao, "Nonparametric estimation of the number of classes in a population",
Scandinavian Journal of Statistics 11 (1984), 265–270.
-/

@[expose] public section

-- Keep the names used by the original wanted module and its blueprint link.
namespace WantedExt.Biology.StatisticalGenetics.ChaoLowerBoundWanted

/-- The expected number `E[f_k] = ∑ᵢ e^{-λᵢ} λᵢᵏ / k!` of classes observed exactly `k` times
when class `i` is observed a Poisson(`λᵢ`) number of times. -/
noncomputable def expectedFreq {S : ℕ} (rate : Fin S → ℝ) (k : ℕ) : ℝ :=
  ∑ i, Real.exp (-rate i) * rate i ^ k / k.factorial

/-- **Chao's lower bound** (Chao 1984; derived for Poisson sampling): let there be `S` classes
with Poisson sampling rates `λᵢ > 0`, and suppose `E[f₂] > 0`. Then the number of classes is at
least the expected number observed plus `E[f₁]² / (2 E[f₂])`:
`E[S_obs] + E[f₁]² / (2 E[f₂]) ≤ S`, where `E[S_obs] = S - E[f₀]`.

Source: Chao (1984). -/
public theorem chao_lower_bound {S : ℕ} (rate : Fin S → ℝ) (hrate : ∀ i, 0 < rate i)
    (h₂ : 0 < expectedFreq rate 2) :
    ((S : ℝ) - expectedFreq rate 0) + expectedFreq rate 1 ^ 2 / (2 * expectedFreq rate 2) ≤ S := by
  have hzero : expectedFreq rate 0 = ∑ i, Real.exp (-rate i) := by simp [expectedFreq]
  have hone : expectedFreq rate 1 = ∑ i, Real.exp (-rate i) * rate i := by simp [expectedFreq]
  have htwo : 2 * expectedFreq rate 2 = ∑ i, Real.exp (-rate i) * rate i ^ 2 := by
    rw [expectedFreq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    norm_num [Nat.factorial_succ]
    ring
  have hs : expectedFreq rate 1 ^ 2 ≤ expectedFreq rate 0 * (2 * expectedFreq rate 2) := by
    rw [hzero, hone, htwo]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => (Real.exp_pos _).le)
      (fun i _ => mul_nonneg (Real.exp_pos _).le (pow_nonneg (hrate i).le _)) ?_
    intro i _
    exact le_of_eq (by ring)
  have hd := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) h₂)).2 hs
  linarith only [hd]

end WantedExt.Biology.StatisticalGenetics.ChaoLowerBoundWanted
