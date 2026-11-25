/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_24.lean` (openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029), for the theorem statement and its description.
Authors: Lushi Pu et al. (MA-ProofBench)
Licensed under the MIT License.

ATLAS renamed the declaration, placed it in a namespace, and added the proof.

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.OfScalars

/-!
# Power series agreeing at reciprocal integers

This file proves that two real power series converging on the open unit interval have equal
coefficients if their sums agree at every reciprocal integer starting at `1 / 2`.
-/

open Filter FormalMultilinearSeries
open scoped Topology ENNReal NNReal

namespace MathlibExt.Analysis.SpecificLimits.PowerSeriesCoeffEqOfAgreeOnReciprocalsWanted

private theorem hasFPowerSeriesAt_tsum (c : ℕ → ℝ)
    (hc : ∀ x : ℝ, |x| < 1 → Summable (fun k : ℕ => c k * x ^ k)) :
    HasFPowerSeriesAt (fun x : ℝ ↦ ∑' k, c k * x ^ k) (ofScalars ℝ c) 0 := by
  have hr : 1 ≤ (ofScalars ℝ c).radius := by
    refine ENNReal.le_of_forall_pos_nnreal_lt fun r _ hr ↦ ?_
    have hr' : (r : ℝ) < 1 := by exact_mod_cast hr
    have hs := hc r (by rwa [abs_of_nonneg r.coe_nonneg])
    apply (ofScalars ℝ c).le_radius_of_tendsto
    simpa only [ofScalars_norm, norm_mul, norm_pow, Real.norm_of_nonneg r.coe_nonneg]
      using hs.tendsto_atTop_zero.norm
  have h := ((ofScalars ℝ c).hasFPowerSeriesOnBall (zero_lt_one.trans_le hr)).hasFPowerSeriesAt
  change HasFPowerSeriesAt (ofScalarsSum c) (ofScalars ℝ c) 0 at h
  simpa only [ofScalarsSum_eq_tsum, smul_eq_mul] using h

/-- **Power series agreeing at $1/2, 1/3, 1/4, \dots$ have equal coefficients.** Let $(a_k)$ and
$(b_k)$ be real sequences such that the series $\sum_{k=0}^{\infty} a_k x^k$ and
$\sum_{k=0}^{\infty} b_k x^k$ converge absolutely for every real $x$ with $|x| < 1$. If
$\sum_{k=0}^{\infty} a_k x^k = \sum_{k=0}^{\infty} b_k x^k$ for $x = 1/2, 1/3, 1/4, \dots$, then
$a_k = b_k$ for all $k \ge 0$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_24.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem coeff_eq_of_tsum_eq_on_inv_nat_add_two
    (a b : ℕ → ℝ) (ha : ∀ x : ℝ, |x| < 1 → Summable (fun k : ℕ => a k * x ^ k))
    (hb : ∀ x : ℝ, |x| < 1 → Summable (fun k : ℕ => b k * x ^ k))
    (hEq : ∀ n : ℕ, (∑' k : ℕ, a k * ((1 : ℝ) / (n + 2)) ^ k) =
      (∑' k : ℕ, b k * ((1 : ℝ) / (n + 2)) ^ k)) :
    ∀ k : ℕ, a k = b k := by
  have hpa := hasFPowerSeriesAt_tsum a ha
  have hpb := hasFPowerSeriesAt_tsum b hb
  have hlim : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 2)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
    · simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 2)
    · exact ne_of_gt (by positivity)
  have heq := (hpa.analyticAt.frequently_eq_iff_eventually_eq hpb.analyticAt).mp
    (hlim.frequently (Eventually.of_forall hEq).frequently)
  have hseries := hpa.eq_formalMultilinearSeries_of_eventually hpb heq
  exact congrFun ((ofScalars_series_eq_iff ℝ a b).mp hseries)

end MathlibExt.Analysis.SpecificLimits.PowerSeriesCoeffEqOfAgreeOnReciprocalsWanted
