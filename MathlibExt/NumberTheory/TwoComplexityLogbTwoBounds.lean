/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TwoComplexityMax

/-!
# Logarithmic bounds for the 2-complexity

For a positive even integer greater than two, halving after removing its remainder modulo four
produces a smaller positive even integer. This yields the upper bound, while the maximum value for a
given number of copies gives the lower bound.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.TwoComplexityWanted

private theorem exists_canBuild_two_le_logb (n : ℕ) (h2n : 2 ∣ n) (hn : 1 ≤ n) :
    ∃ k : ℕ, CanBuild 2 k n ∧ (k : ℝ) ≤ 2 * Real.logb 2 n - 1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hbase : n = 2
    · subst n
      exact ⟨1, CanBuild.base, by norm_num [Real.logb_self_eq_one]⟩
    have log_step (m : ℕ) (hm : 1 ≤ m) (hmn : 2 * m ≤ n) :
        1 + Real.logb 2 m ≤ Real.logb 2 n := by
      calc
        1 + Real.logb 2 m = Real.logb 2 (2 * (m : ℝ)) := by
          rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast (show m ≠ 0 by omega)),
            Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        _ ≤ Real.logb 2 n := by
          apply Real.logb_le_logb_of_le (by norm_num)
          · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
            positivity
          · exact_mod_cast hmn
    by_cases h4n : 4 ∣ n
    · have hm : 1 ≤ n / 2 := by omega
      have heq : 2 * (n / 2) = n := by omega
      obtain ⟨k, hk, hbound⟩ := ih (n / 2) (by omega) (by omega) hm
      refine ⟨1 + k, ?_, ?_⟩
      · simpa only [heq] using CanBuild.base.mul hk
      · push_cast
        linarith only [hbound, log_step (n / 2) hm heq.le]
    · have hm : 1 ≤ (n - 2) / 2 := by omega
      have heq : 2 * ((n - 2) / 2) + 2 = n := by omega
      obtain ⟨k, hk, hbound⟩ := ih ((n - 2) / 2) (by omega) (by omega) hm
      refine ⟨1 + k + 1, ?_, ?_⟩
      · simpa only [heq] using (CanBuild.base.mul hk).add CanBuild.base
      · push_cast
        linarith only [hbound, log_step ((n - 2) / 2) hm (by omega)]

/-- **Logarithmic bounds for the 2-complexity (Zhang's Lemma 3(3)).** Write $\|n\|_2$ for the
2-complexity of $n$: the least number of copies of $2$ from which $n$ can be built using addition
and multiplication, and $0$ if $n$ cannot be built. For every even natural number $n \ge 1$,
$\log_2 n \le \|n\|_2 \le 2 \log_2 n - 1$, where $\log_2$ is the real base-2 logarithm.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Lemma 3. -/
public theorem logb_two_bounds (n : ℕ) (h2n : 2 ∣ n)
    (hn : 1 ≤ n) :
    Real.logb 2 n ≤ (complexityL 2 n : ℝ) ∧
      (complexityL 2 n : ℝ) ≤ 2 * Real.logb 2 n - 1 := by
  obtain ⟨k, hk, hbound⟩ := exists_canBuild_two_le_logb n h2n hn
  refine ⟨?_, (show (complexityL 2 n : ℝ) ≤ k by exact_mod_cast complexityL_min_le hk).trans hbound⟩
  have hmin := complexityL_spec ⟨k, hk⟩
  have hmax := (canBuild_max 2 (complexityL 2 n) (by decide) hmin.one_le).2 n hmin
  calc
    Real.logb 2 n ≤ Real.logb 2 ((2 : ℝ) ^ complexityL 2 n) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hn) (by exact_mod_cast hmax)
    _ = (complexityL 2 n : ℝ) := by simp [Real.logb_pow, Real.logb_self_eq_one]

end MathlibExt.NumberTheory.TwoComplexityWanted
