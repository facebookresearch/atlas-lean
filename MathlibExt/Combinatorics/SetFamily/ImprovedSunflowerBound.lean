/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The definition `lowerBound` comes from `LeanEval.Combinatorics.ImprovedBoundsSunflowerLemma`.
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer

Source: leanprover/lean-eval, commit 38361be884302c7edce1908c4aef8296eb2cb27e, problem
`annals_improved_bounds_sunflower_lemma`. The benchmark credits
ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14),
`AnnalsChallenge/AnnalsOfMathematics/2021-194-3-ImprovedBoundsSunflowerLemma.lean`.
The formula is unchanged; the explicit constant and its comparison proof are new.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An absolute constant for the Alweiss–Lovett–Wu–Zhang sunflower bound

Alweiss, Lovett, Wu and Zhang, *Improved bounds for the sunflower lemma*, Theorem 1.4
([arXiv:1908.08483v3](https://arxiv.org/abs/1908.08483v3)), do not specify a numerical value.
Kupavskii and Zakharov, *Spread approximations for forbidden intersections problems*, §2,
(1) ([arXiv:2203.13379v3](https://arxiv.org/abs/2203.13379v3)), give the strict threshold
`(2 ^ 10 * r * logb 2 (w * r)) ^ w` for a family of distinct sets of size exactly `w`.

The comparison below is strict, so a weak size hypothesis at the ALWZ threshold suffices.
To use the uniform result on a finite ground set with sets of size *at most* `w`, add to each
member `A` exactly `w - |A|` new points private to `A`. Intersecting a padded set with the old
ground set recovers `A`, so cardinality is preserved. No new point belongs to two padded sets;
thus pairwise and total intersections in any subfamily of at least two sets are unchanged.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ImprovedBoundsSunflowerLemma

open Real

/-- **Sunflower lower bound.** For natural numbers $r$ and $w$ and a real number $C$, the lower
bound is the real number
$$\left(C\, r^3 \log_{1.9} w \, \log_{1.9}(\log_{1.9} w)\right)^w,$$
where $\log_{1.9} x = \ln x / \ln 1.9$, with the convention $\ln 0 = 0$.

Following the authors, logarithms are taken to base $1.9$; see the paragraph directly after
Theorem 1.4 of Alweiss, Lovett, Wu, and Zhang, *Improved bounds for the sunflower lemma*. -/
noncomputable def lowerBound (r : ℕ) (C : ℝ) (w : ℕ) : ℝ :=
  (C * r ^ 3 * logb 1.9 w * logb 1.9 (logb 1.9 w)) ^ w

/-- **Sunflower constant.** The real number $2^{14}$ is one absolute constant for the
Alweiss–Lovett–Wu–Zhang bound. The factor $2^{10}$ comes from Kupavskii and Zakharov, §2,
(1); the factor $16$ absorbs the iterated base-$1.9$ logarithm even at width $2$. -/
noncomputable def C : ℝ := 2 ^ 14

private lemma one_lt_sixteen_mul_loglog {w : ℕ} (hw : 2 ≤ w) :
    1 < 16 * logb 1.9 (logb 1.9 w) := by
  have hb : (1 : ℝ) < 1.9 := by norm_num
  -- Two rational power comparisons avoid any rounded evaluation of a logarithm.
  have h₁ := logb_lt_logb hb (by norm_num : 0 < (1.9 : ℝ) ^ 17)
    (by norm_num : (1.9 : ℝ) ^ 17 < 2 ^ 16)
  have h₂ := logb_lt_logb hb (by norm_num : (0 : ℝ) < 1.9)
    (by norm_num : (1.9 : ℝ) < (17 / 16) ^ 16)
  rw [logb_pow, logb_self_eq_one hb, logb_pow] at h₁
  rw [logb_self_eq_one hb, logb_pow] at h₂
  have hw' := logb_le_logb_of_le hb (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ w by exact_mod_cast hw)
  have h := logb_le_logb_of_le hb (by norm_num : (0 : ℝ) < 17 / 16)
    (show (17 / 16 : ℝ) ≤ logb 1.9 w by linarith)
  linarith

/-- **Strict comparison of sunflower thresholds.** For $r\ge3$ and $w\ge2$, the explicit
uniform sunflower threshold $(2^{10}r\log_2(wr))^w$ is strictly less than the
Alweiss–Lovett–Wu–Zhang threshold with $C=2^{14}$.

Source for the uniform threshold: A. Kupavskii and D. Zakharov, *Spread approximations for
forbidden intersections problems*, [arXiv:2203.13379v3](https://arxiv.org/abs/2203.13379v3),
§2, (1). -/
theorem uniformThreshold_lt_lowerBound {r w : ℕ} (hr : 3 ≤ r) (hw : 2 ≤ w) :
    ((2 : ℝ) ^ 10 * r * logb 2 ((w : ℝ) * r)) ^ w < lowerBound r C w := by
  have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hw' : (2 : ℝ) ≤ w := by exact_mod_cast hw
  have hb : (1 : ℝ) < 1.9 := by norm_num
  have hL : 1 ≤ logb 1.9 w := by
    rw [← logb_self_eq_one hb]
    exact logb_le_logb_of_le hb (by norm_num) (by linarith)
  have hbase : logb 2 w ≤ logb 1.9 w := by
    exact div_le_div_of_nonneg_left (log_nonneg (by linarith)) (log_pos hb)
      (log_le_log (by norm_num) (by norm_num))
  have hpow : (r : ℝ) ≤ 2 ^ r := by exact_mod_cast (Nat.lt_two_pow_self (n := r)).le
  have hlogr : logb 2 r ≤ r := by
    simpa only [logb_pow, logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using
      logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hpow
  have hlog : logb 2 ((w : ℝ) * r) ≤ r ^ 2 * logb 1.9 w := by
    rw [logb_mul (by positivity) (by positivity)]
    calc logb 2 w + logb 2 r ≤ logb 1.9 w + r * logb 1.9 w := by
           exact add_le_add hbase (hlogr.trans (le_mul_of_one_le_right (by positivity) hL))
         _ ≤ r ^ 2 * logb 1.9 w := by
           rw [← one_add_mul]; gcongr; nlinarith
  have hnonneg : 0 ≤ logb 2 ((w : ℝ) * r) := logb_nonneg (by norm_num) (by nlinarith)
  apply pow_lt_pow_left₀ _ (by positivity) (by omega : w ≠ 0)
  calc 2 ^ 10 * r * logb 2 ((w : ℝ) * r) ≤ 2 ^ 10 * r * (r ^ 2 * logb 1.9 w) := by gcongr
       _ < 2 ^ 10 * r * (r ^ 2 * logb 1.9 w) * (16 * logb 1.9 (logb 1.9 w)) :=
         lt_mul_of_one_lt_right (by positivity) (one_lt_sixteen_mul_loglog hw)
       _ = C * r ^ 3 * logb 1.9 w * logb 1.9 (logb 1.9 w) := by unfold C; ring

end MathlibExt.Combinatorics.ImprovedBoundsSunflowerLemma
