/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.RiordanNumber
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Function.L2Space
import MathlibExt.Probability.Distributions.Semicircle

/-!
# Log-convexity of the even-indexed Riordan numbers

The Riordan numbers are the moments of `x² - 1` under the semicircle law.
Cauchy–Schwarz for its powers gives log-convexity of the even-indexed terms.
-/

namespace MetaMathlibExt

open MeasureTheory ProbabilityTheory

namespace riordanNumber_even_logConvex

private lemma integrable_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f semicircleReal := by
  have h := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr semicircleReal_compl_Icc)
  rw [← h]
  exact hf.integrableOn_Icc

private lemma integral_pow_sub_one (n : ℕ) :
    ∫ x, (x ^ 2 - 1) ^ n ∂semicircleReal = (riordanNumber n : ℝ) := by
  simp_rw [sub_eq_add_neg, add_pow, ← pow_mul]
  rw [integral_finsetSum _ (fun k _ => integrable_of_continuous (by fun_prop)), riordanNumber]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const, integral_mul_const, integral_pow_two_mul_semicircleReal]
  ring

end riordanNumber_even_logConvex

open riordanNumber_even_logConvex in
/-- **Log-convexity of the even-indexed Riordan numbers.** Let $r_n$ denote the $n$-th Riordan
number. The even-indexed Riordan numbers $r_0, r_2, r_4, \dots$ form a log-convex sequence: for
every natural number $n$,
$$r_{2n+2}^2 \le r_{2n} \, r_{2n+4}.$$

The Riordan numbers begin $1, 0, 1, 1, 3, 6, 15, \dots$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Corollary 1
(`integers-2026-A55-cor-1`). -/
public theorem riordanNumber_even_logConvex (n : ℕ) :
    riordanNumber (2 * (n + 1)) ^ 2 ≤
      riordanNumber (2 * n) * riordanNumber (2 * (n + 2)) := by
  let f (k : ℕ) (x : ℝ) := (x ^ 2 - 1) ^ k
  have hf (k : ℕ) : MemLp (f k) 2 semicircleReal := by
    apply (memLp_two_iff_integrable_sq (by dsimp [f]; fun_prop)).2
    exact integrable_of_continuous (by dsimp [f]; fun_prop)
  let v (k : ℕ) := (hf k).toLp (f k)
  have hinner (i j : ℕ) : inner ℝ (v i) (v j) = (riordanNumber (i + j) : ℝ) := by
    rw [L2.inner_def, ← integral_pow_sub_one]
    apply integral_congr_ae
    filter_upwards [(hf i).coeFn_toLp, (hf j).coeFn_toLp] with x hi hj
    simp only [v, Real.inner_apply, hi, hj, f, pow_add]
  have h := real_inner_mul_inner_self_le (v n) (v (n + 2))
  simp only [hinner] at h
  rw [show n + (n + 2) = 2 * (n + 1) by omega, ← two_mul, ← two_mul] at h
  rw [← sq] at h
  exact_mod_cast h

end MetaMathlibExt
