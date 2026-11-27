/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Uniformly large level sets under an L^2 <= C L^1 bound

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_04.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_04 … := by sorry` into the Batteries `theorem_wanted`
`exists_tendsto_atTop_inf_measure_levelSet_pos`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.LargeLevelSetReverseHolderWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; added docstrings to helper definitions;
corrected the statement: replaced the target filter `atTop` of the divergence hypothesis
`hL1_div` by `nhds ⊤`; in `ℝ≥0∞`, `atTop = pure ⊤`, so the source hypothesis forced `‖f n‖₁ = ∞`
eventually, contradicting `MemLp (f n) 2`, and made the statement vacuous. This move supplies a
proof of the corrected ATLAS statement using Hölder's inequality on the superlevel set.
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Uniformly large superlevel sets under a reverse Hölder bound -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MathlibExt.MeasureTheory.LargeLevelSetReverseHolderWanted

/-- **Lebesgue measure on the unit interval.** The measure on $\mathbb{R}$ that assigns to each
set $A \subseteq \mathbb{R}$ the Lebesgue measure of $A \cap [0,1]$.
-/
noncomputable abbrev μIcc01 : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- **Uniformly large level sets under a reverse Hölder bound.** Let $\mu$ be Lebesgue measure
on $[0,1]$, and let $f_0, f_1, f_2, \ldots : \mathbb{R} \to \mathbb{R}$ lie in $L^2(\mu)$ with
$\|f_n\|_{L^2(\mu)} \le 2024\,\|f_n\|_{L^1(\mu)}$ for every $n$ and
$\|f_n\|_{L^1(\mu)} \to \infty$ as $n \to \infty$. Then there is a sequence of real numbers
$y_n \to \infty$ such that
$$
\inf_n \mu(\{x : |f_n(x)| \ge y_n\}) > 0.
$$

The divergence hypothesis is the limit $\|f_n\|_{L^1(\mu)} \to \infty$ in $[0,\infty]$; the
formal source instead required $\|f_n\|_{L^1(\mu)} = \infty$ for all large $n$, which no function
in $L^2(\mu)$ satisfies, so its statement was vacuous.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_04.lean` at
openbmb/ma-proofbench@31bab4c, with the change above.
-/
theorem exists_tendsto_atTop_inf_measure_levelSet_pos
    (f : ℕ → ℝ → ℝ)
    (hf_L2 : ∀ n : ℕ, MemLp (f n) 2 μIcc01)
    (hbound : ∀ n : ℕ,
      eLpNorm (f n) 2 μIcc01 ≤
        ENNReal.ofReal 2024 * eLpNorm (f n) 1 μIcc01)
    (hL1_div : Tendsto (fun n : ℕ => eLpNorm (f n) 1 μIcc01) atTop (nhds ⊤)) :
    ∃ y : ℕ → ℝ,
      Tendsto y atTop atTop ∧
      0 < sInf (Set.range (fun n : ℕ =>
        μIcc01 {x : ℝ | |f n x| ≥ y n})) := by
  have hmass : μIcc01 univ = 1 := by
    rw [μIcc01, Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
  let : IsProbabilityMeasure μIcc01 := ⟨hmass⟩
  let L (n : ℕ) := eLpNorm (f n) 1 μIcc01
  let y (n : ℕ) := (L n).toReal / 2
  have hfin (n : ℕ) : L n ≠ ∞ := ((hf_L2 n).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).ne
  refine ⟨y, tendsto_atTop.mpr fun b => ?_, ?_⟩
  · have he : ∀ᶠ n in atTop, ENNReal.ofReal (2 * max b 0) < L n :=
      hL1_div.eventually_const_lt ENNReal.ofReal_lt_top
    filter_upwards [he] with n hn
    have ht := (ENNReal.ofReal_lt_iff_lt_toReal (mul_nonneg (by norm_num) (le_max_right b 0))
      (hfin n)).mp hn
    dsimp [y]
    linarith [le_max_left b (0 : ℝ)]
  let d : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ * (2024 : ℝ≥0∞)⁻¹
  have hd0 : 0 < d := by
    dsimp [d]
    exact pos_iff_ne_zero.mpr (mul_ne_zero (by simp) (by simp))
  have hd1 : d ≤ 1 := by
    calc
      d ≤ 1 * 1 := mul_le_mul' (ENNReal.inv_le_one.mpr (by norm_num))
        (ENNReal.inv_le_one.mpr (by norm_num))
      _ = 1 := one_mul _
  refine (pow_ne_zero 2 hd0.ne').bot_lt.trans_le (le_sInf ?_)
  rintro _ ⟨n, rfl⟩
  let s : Set ℝ := {x | y n ≤ |f n x|}
  change d ^ 2 ≤ μIcc01 s
  by_cases h0 : L n = 0
  · have hs : s = univ := by ext x; simp [s, y, h0]
    rw [hs, hmass]
    simpa using pow_le_pow_left' hd1 2
  have hf := (hf_L2 n).aestronglyMeasurable
  have hsm : NullMeasurableSet s μIcc01 := by
    simpa only [s, Real.norm_eq_abs] using
      (nullMeasurableSet_le (f := fun _ : ℝ => y n) aemeasurable_const hf.norm.aemeasurable)
  have hy : ENNReal.ofReal (y n) = L n / 2 := by
    change ENNReal.ofReal ((L n).toReal / 2) = L n / 2
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_toReal (hfin n), show ENNReal.ofReal 2 = 2 by norm_num]
  have hsml : (∫⁻ x in sᶜ, ‖f n x‖ₑ ∂μIcc01) ≤ L n / 2 := by
    calc
      (∫⁻ x in sᶜ, ‖f n x‖ₑ ∂μIcc01) ≤ ∫⁻ _ in sᶜ, ENNReal.ofReal (y n) ∂μIcc01 := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem₀ hsm.compl] with x hx
        have hx' : |f n x| ≤ y n := (lt_of_not_ge hx).le
        rw [← ofReal_norm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal hx'
      _ = (L n / 2) * μIcc01 sᶜ := by rw [lintegral_const, Measure.restrict_apply_univ, hy]
      _ ≤ (L n / 2) * 1 := mul_le_mul' le_rfl ((measure_mono (subset_univ _)).trans_eq hmass)
      _ = L n / 2 := mul_one _
  have hlarge : (∫⁻ x in s, ‖f n x‖ₑ ∂μIcc01) ≤
      ((2024 : ℝ≥0∞) * L n) * μIcc01 s ^ (1 / 2 : ℝ) := by
    rw [← eLpNorm_one_eq_lintegral_eNorm hf.restrict]
    have he : 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μIcc01.restrict s) (f := f n)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf.restrict
    rw [Measure.restrict_apply_univ, he] at h
    apply h.trans
    exact mul_le_mul' ((eLpNorm_restrict_le (f n) 2 μIcc01 s).trans
      (by simpa [L] using hbound n)) le_rfl
  have hL : L n ≤ L n / 2 + ((2024 : ℝ≥0∞) * L n) * μIcc01 s ^ (1 / 2 : ℝ) := by
    calc
      L n = (∫⁻ x in sᶜ, ‖f n x‖ₑ ∂μIcc01) + ∫⁻ x in s, ‖f n x‖ₑ ∂μIcc01 := by
        rw [add_comm, lintegral_add_compl₀ _ hsm, ← eLpNorm_one_eq_lintegral_eNorm hf]
      _ ≤ _ := add_le_add hsml hlarge
  -- If the mass is too small, each contribution is at most half the full L¹ norm,
  -- and the contribution of the superlevel set is strictly smaller.
  by_contra hsmall
  have hroot : μIcc01 s ^ (1 / 2 : ℝ) < d := by
    have h := (ENNReal.rpow_lt_rpow_iff (z := (1 / 2 : ℝ)) (by norm_num)).mpr
      (lt_of_not_ge hsmall : μIcc01 s < d ^ 2)
    rwa [← ENNReal.rpow_natCast d 2, ← ENNReal.rpow_mul,
      show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one] at h
  have hc : ((2024 : ℝ≥0∞) * L n) ≠ 0 := mul_ne_zero (by simp) h0
  have hct : ((2024 : ℝ≥0∞) * L n) ≠ ∞ := ENNReal.mul_ne_top (by simp) (hfin n)
  have hstrict := ENNReal.mul_lt_mul_right hc hct hroot
  have hcancel : ((2024 : ℝ≥0∞) * L n) * d = L n / 2 := by
    change ((2024 : ℝ≥0∞) * L n) * (2⁻¹ * 2024⁻¹) = L n / 2
    rw [ENNReal.div_eq_inv_mul]
    calc
      ((2024 : ℝ≥0∞) * L n) * (2⁻¹ * 2024⁻¹) =
          (2024 * 2024⁻¹) * (2⁻¹ * L n) := by ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  have hhalf : L n / 2 + L n / 2 = L n := by
    rw [ENNReal.div_eq_inv_mul, ← add_mul, ← two_mul,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  have hhfin : L n / 2 ≠ ∞ := by
    rw [ENNReal.div_eq_inv_mul]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by simp)) (hfin n)
  rw [hcancel] at hstrict
  have hlt := ENNReal.add_lt_add_left hhfin hstrict
  rw [hhalf] at hlt
  exact hlt.not_ge hL

end MathlibExt.MeasureTheory.LargeLevelSetReverseHolderWanted
