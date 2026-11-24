/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Uniform Lp bounds for all p ≥ 1 give the same L∞ bound on [0,1]

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_52.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
The same formal statement appears in the Hugging Face dataset openbmb/MA-ProofBench.
Changes made: converted
`theorem ma_proofbench_l2_52 … := by sorry` into the Batteries `theorem_wanted`
`eLpNorm_top_le_of_forall_one_le_eLpNorm_le`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.LinftyNormLeSupLpNormUnitIntervalWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system. The move to this proved module supplies a proof
and narrows the imports, without changing the ATLAS name or statement.
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-! # Uniform finite-exponent bounds imply an essential-supremum bound -/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace MathlibExt.MeasureTheory.LinftyNormLeSupLpNormUnitIntervalWanted

/-- **Uniform $L^p$ bounds on $[0,1]$ give the same $L^\infty$ bound.** Let $M$ be a real number,
write $M^+ = \max(M, 0)$, and let $f_0, f_1, f_2, \dots : \mathbb{R} \to \mathbb{R}$ be functions
that are almost everywhere strongly measurable with respect to Lebesgue measure restricted to
$[0,1]$. If $\|f_n\|_{L^p[0,1]} \le M^+$ for every $n$ and every real $p \ge 1$, then
$\|f_n\|_{L^\infty[0,1]} \le M^+$ for every $n$. All norms are taken with respect to Lebesgue
measure restricted to $[0,1]$ and may be infinite.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_52.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem eLpNorm_top_le_of_forall_one_le_eLpNorm_le
    (f : ℕ → ℝ → ℝ) (M : ℝ)
    (hf : ∀ n : ℕ, AEStronglyMeasurable (f n) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hM : ∀ n : ℕ, ∀ p : ℝ, 1 ≤ p →
      eLpNorm (f n) (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) ≤ ENNReal.ofReal M) :
    ∀ n : ℕ, eLpNorm (f n) ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1)) ≤ ENNReal.ofReal M := by
  intro n
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  change eLpNorm (f n) ∞ μ ≤ ENNReal.ofReal M
  rw [eLpNorm_exponent_top (hf n)]
  by_contra! h
  obtain ⟨c, hc, hlt⟩ := exists_between h
  have hc0 : c ≠ 0 := (zero_le.trans_lt hc).ne'
  have hc_top : c ≠ ∞ := (hlt.trans_le le_top).ne
  let r := c⁻¹ * ENNReal.ofReal M
  have hr : r < 1 := by
    rw [← ENNReal.inv_mul_cancel hc0 hc_top]
    exact ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr hc_top)
      (ENNReal.inv_ne_top.mpr hc0) hc
  let s : Set ℝ := {x | c ≤ ‖f n x‖ₑ}
  -- Integer exponents are enough: the upper bound for this superlevel set decays geometrically.
  have htail (k : ℕ) : μ s ≤ r ^ (k + 1) := by
    have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    have hB : eLpNorm (f n) (↑(k + 1 : ℕ) : ℝ≥0∞) μ ≤ ENNReal.ofReal M := by
      simpa only [ENNReal.ofReal_natCast] using hM n _ hk
    calc
      μ s ≤ c⁻¹ ^ (((k + 1 : ℕ) : ℝ≥0∞).toReal) *
          eLpNorm (f n) (↑(k + 1 : ℕ) : ℝ≥0∞) μ ^ (((k + 1 : ℕ) : ℝ≥0∞).toReal) :=
        meas_ge_le_mul_pow_eLpNorm_eNorm μ (by simp) (ENNReal.natCast_ne_top _) hc0
          (fun htop => (hc_top htop).elim)
      _ ≤ r ^ (k + 1) := by
        rw [ENNReal.toReal_natCast, ENNReal.rpow_natCast, ENNReal.rpow_natCast]
        dsimp [r]
        rw [mul_pow]
        gcongr
  have hs : μ s = 0 := le_antisymm
    (ge_of_tendsto ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr).comp
      (tendsto_add_atTop_nat 1)) (Eventually.of_forall htail)) zero_le
  have hae : ∀ᵐ x ∂μ, ‖f n x‖ₑ < c := by
    rw [ae_iff]
    simpa only [s, not_lt] using hs
  exact hlt.not_ge (eLpNormEssSup_le_of_ae_eNorm_bound (hae.mono fun _ hx => hx.le))

end MathlibExt.MeasureTheory.LinftyNormLeSupLpNormUnitIntervalWanted
