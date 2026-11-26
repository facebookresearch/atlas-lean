/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# An a.e. null sequence on [0,1] survives unbounded scalar multipliers

The following OpenBMB notice applies to the adapted statement and its documentation.

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

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_38.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_38 … := by sorry` into the Batteries `theorem_wanted`
`exists_tendsto_abs_atTop_and_ae_tendsto_mul_zero`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.AeNullSequenceUnboundedMultipliersWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system. The move to this proved module supplies a
proof using Egorov's theorem and Borel–Cantelli, without changing the ATLAS name or statement.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic.Positivity

/-! # Unbounded multipliers for almost-everywhere null sequences -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MathlibExt.MeasureTheory.AeNullSequenceUnboundedMultipliersWanted

/-- **Unbounded multipliers preserving almost-everywhere convergence to zero.** Let
$(f_n)_{n \in \mathbb{N}}$ be a sequence of Borel measurable functions $f_n : \mathbb{R} \to
\mathbb{R}$ such that $f_n(x) \to 0$ for almost every $x \in [0, 1]$. Then there is a sequence of
real numbers $(c_n)_{n \in \mathbb{N}}$ with $|c_n| \to \infty$ such that $c_n f_n(x) \to 0$ for
almost every $x \in [0, 1]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_38.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem exists_tendsto_abs_atTop_and_ae_tendsto_mul_zero (f : ℕ → ℝ → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_ae : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      Filter.Tendsto (fun n => f n x) Filter.atTop (nhds 0)) :
    ∃ c : ℕ → ℝ,
      Filter.Tendsto (fun n => |c n|) Filter.atTop Filter.atTop ∧
      (∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        Filter.Tendsto (fun n => c n * f n x) Filter.atTop (nhds 0)) := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let : IsFiniteMeasure μ := ⟨by
    change volume.restrict (Icc (0 : ℝ) 1) univ < ∞
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  let r : ℝ≥0∞ := 2⁻¹
  have hr_pos : 0 < r := ENNReal.inv_pos.mpr (by simp)
  have hr_lt : r < 1 := by
    simpa only [r, inv_one] using ENNReal.inv_lt_inv.mpr ENNReal.one_lt_two
  -- Give each precision level a summable exceptional-set budget.
  have hlevel (k : ℕ) : ∃ s : Set ℝ, μ s ≤ r ^ k ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ x ∉ s, |f n x| < (((k : ℝ) + 1)⁻¹) ^ 2 := by
    obtain ⟨s, _, hmass, hu⟩ := tendstoUniformlyOn_of_ae_tendsto'
      (fun n => (hf_meas n).aestronglyMeasurable) hf_ae
      (pos_iff_ne_zero.mpr (pow_ne_zero k hr_pos.ne'))
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((Metric.tendstoUniformlyOn_iff.mp hu) _ (by positivity :
        0 < (((k : ℝ) + 1)⁻¹) ^ 2))
    refine ⟨s, hmass, N, fun n hn x hx => ?_⟩
    simpa only [dist_comm, Real.dist_eq, sub_zero] using hN n hn x hx
  choose s hmass N htail using hlevel
  have hsum : (∑' k : ℕ, μ (s k)) < ∞ := by
    refine (tsum_le_tsum hmass).trans_lt ?_
    rw [ENNReal.tsum_geometric, lt_top_iff_ne_top, ENNReal.inv_ne_top]
    exact (tsub_pos_iff_lt.mpr hr_lt).ne'
  -- Take the largest eligible precision level below n. Every fixed level is eventually eligible.
  let m (n : ℕ) := Nat.findGreatest (fun k => N k ≤ n) n
  have hm : Tendsto m atTop atTop := tendsto_atTop.mpr fun k =>
    (eventually_ge_atTop (max k (N k))).mono fun n hn =>
      Nat.le_findGreatest ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
  have hN : ∀ᶠ n in atTop, N (m n) ≤ n :=
    (eventually_ge_atTop (N 0)).mono fun n hn =>
      Nat.findGreatest_spec (P := fun k => N k ≤ n) (m := 0) (Nat.zero_le n) hn
  let c (n : ℕ) := (m n : ℝ) + 1
  have hc_pos (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  have hc : Tendsto c atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop.comp hm)
  refine ⟨c, ?_, ?_⟩
  · simpa only [abs_of_nonneg (le_of_lt (hc_pos _))] using hc
  · filter_upwards [ae_eventually_notMem hsum.ne] with x hx
    have hinv : Tendsto (fun n => (c n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hc
    refine squeeze_zero_norm' ?_ hinv
    filter_upwards [hN, hm.eventually hx] with n hn hxn
    have hb : |f n x| ≤ (c n)⁻¹ ^ 2 := (htail (m n) n hn x hxn).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc_pos n).le]
    calc
      c n * |f n x| ≤ c n * (c n)⁻¹ ^ 2 := mul_le_mul_of_nonneg_left hb (hc_pos n).le
      _ = (c n)⁻¹ := by rw [pow_two, ← mul_assoc, mul_inv_cancel₀ (hc_pos n).ne', one_mul]

end MathlibExt.MeasureTheory.AeNullSequenceUnboundedMultipliersWanted
