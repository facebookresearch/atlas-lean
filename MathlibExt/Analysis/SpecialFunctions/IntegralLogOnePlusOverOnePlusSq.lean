/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# ∫₀¹ log(1+x)/(1+x²) dx = (π/8) log 2

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_58.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_58 … := by sorry` into the Batteries `theorem_wanted`
`integral_log_one_add_div_one_add_sq`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.SpecialFunctions.IntegralLogOnePlusOverOnePlusSqWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Serret's integral

The substitution `x ↦ (1 - x) / (1 + x)` reverses the integration interval and preserves
`dx / (1 + x²)` up to orientation. The original and reflected logarithms sum to `log 2`,
so their sum is evaluated by the antiderivative `arctan`.
-/

public section

open Set intervalIntegral
open scoped Interval

namespace MathlibExt.Analysis.SpecialFunctions.IntegralLogOnePlusOverOnePlusSqWanted

/-- **Serret's integral.** With $\log$ the natural logarithm,

$$\int_0^1 \frac{\log(1+x)}{1+x^2}\,dx = \frac{\pi}{8}\log 2.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_58.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem integral_log_one_add_div_one_add_sq
    : (∫ x in 0..1, Real.log (1 + x) / (1 + x ^ 2))
      =
    (Real.pi / 8) * Real.log 2 := by
  -- This substitution reverses `[0, 1]` and preserves the arctangent weight up to sign.
  let T (x : ℝ) := (1 - x) / (1 + x)
  let D (x : ℝ) := -2 / (1 + x) ^ 2
  let w (x : ℝ) := (1 + x ^ 2)⁻¹
  let g (x : ℝ) := Real.log (1 + x) * w x
  let gr (x : ℝ) := Real.log (1 + T x) * w x
  have hpos (x : ℝ) (hx : x ∈ [[(0 : ℝ), 1]]) : 0 < 1 + x := by
    rw [uIcc_of_le zero_le_one] at hx
    linarith [hx.1]
  have hmap : MapsTo T [[(0 : ℝ), 1]] [[(0 : ℝ), 1]] := by
    intro x hx
    have hp := hpos x hx
    rw [uIcc_of_le zero_le_one] at hx ⊢
    change 0 ≤ (1 - x) / (1 + x) ∧ (1 - x) / (1 + x) ≤ 1
    exact ⟨div_nonneg (sub_nonneg.mpr hx.2) hp.le, (div_le_iff₀ hp).2 (by linarith [hx.1])⟩
  have hT0 : T 0 = 1 := by norm_num [T]
  have hT1 : T 1 = 0 := by norm_num [T]
  have hderiv (x : ℝ) (hx : x ∈ [[(0 : ℝ), 1]]) : HasDerivAt T (D x) x := by
    have hn : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id x).const_sub 1
    have hd : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
    change HasDerivAt (fun y : ℝ => (1 - y) / (1 + y)) (D x) x
    convert hn.fun_div hd (ne_of_gt (hpos x hx)) using 1
    dsimp [D]
    ring
  have hDcont : ContinuousOn D [[(0 : ℝ), 1]] := by
    apply continuousOn_const.div (((continuous_const.add continuous_id).pow 2).continuousOn)
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (hpos x hx))
  have hwcont : Continuous w := by
    change Continuous (fun x : ℝ => (1 + x ^ 2)⁻¹)
    have hbase : Continuous (fun x : ℝ => 1 + x ^ 2) := by fun_prop
    exact hbase.inv₀ (fun x => by positivity)
  have hlogcont : ContinuousOn (fun x : ℝ => Real.log (1 + x)) [[(0 : ℝ), 1]] := by
    apply Real.continuousOn_log.comp (continuous_const.add continuous_id).continuousOn
    intro x hx
    change (1 + x) ≠ 0
    exact ne_of_gt (hpos x hx)
  have hgcont : ContinuousOn g [[(0 : ℝ), 1]] := hlogcont.mul hwcont.continuousOn
  have hTcont : ContinuousOn T [[(0 : ℝ), 1]] :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hgrcont : ContinuousOn gr [[(0 : ℝ), 1]] :=
    (hlogcont.comp hTcont hmap).mul hwcont.continuousOn
  have hweight (x : ℝ) (hx : x ∈ [[(0 : ℝ), 1]]) : w (T x) * D x = -w x := by
    have hne := ne_of_gt (hpos x hx)
    have h1 : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
    have h2 : (1 : ℝ) + ((1 - x) / (1 + x)) ^ 2 ≠ 0 := by positivity
    dsimp [w, T, D]
    field_simp [hne, h1, h2]
    ring
  have hsub : (∫ x in (0 : ℝ)..1, (g ∘ T) x * D x) = -(∫ x in (0 : ℝ)..1, g x) := by
    have h := integral_comp_mul_deriv' hderiv hDcont
      (hgcont.mono (image_subset_iff.mpr hmap))
    rw [hT0, hT1] at h
    rw [← integral_symm]
    exact h
  have href : (∫ x in (0 : ℝ)..1, gr x) = ∫ x in (0 : ℝ)..1, g x := by
    have h : (∫ x in (0 : ℝ)..1, (g ∘ T) x * D x) = -(∫ x in (0 : ℝ)..1, gr x) := by
      rw [← integral_neg]
      apply integral_congr
      intro x hx
      change Real.log (1 + T x) * w (T x) * D x = -(Real.log (1 + T x) * w x)
      rw [mul_assoc, hweight x hx, mul_neg]
    exact neg_injective (h.symm.trans hsub)
  -- The two logarithms combine to `log 2`, leaving the arctangent integral.
  have hsum : (∫ x in (0 : ℝ)..1, g x) + (∫ x in (0 : ℝ)..1, gr x) =
      Real.log 2 * (Real.pi / 4) := calc
    _ = ∫ x in (0 : ℝ)..1, g x + gr x :=
      (integral_add hgcont.intervalIntegrable hgrcont.intervalIntegrable).symm
    _ = ∫ x in (0 : ℝ)..1, Real.log 2 * w x := by
      apply integral_congr
      intro x hx
      have hm : (1 + x) * (1 + T x) = 2 := by
        dsimp [T]
        field_simp [ne_of_gt (hpos x hx)]
        ring
      change Real.log (1 + x) * w x + Real.log (1 + T x) * w x = Real.log 2 * w x
      rw [← add_mul, ← Real.log_mul (ne_of_gt (hpos x hx)) (ne_of_gt (hpos (T x) (hmap hx))), hm]
    _ = _ := by
      rw [integral_const_mul]
      change Real.log 2 * (∫ x in (0 : ℝ)..1, (1 + x ^ 2)⁻¹) = _
      rw [integral_inv_one_add_sq, Real.arctan_one, Real.arctan_zero, sub_zero]
  rw [href] at hsum
  have hval : (∫ x in (0 : ℝ)..1, g x) = (Real.pi / 8) * Real.log 2 := calc
    _ = (Real.log 2 * (Real.pi / 4)) / 2 := by linarith
    _ = _ := by ring
  simpa only [g, w, div_eq_mul_inv] using hval

end MathlibExt.Analysis.SpecialFunctions.IntegralLogOnePlusOverOnePlusSqWanted
