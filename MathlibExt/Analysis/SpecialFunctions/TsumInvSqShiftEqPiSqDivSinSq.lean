/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_09.lean` (openbmb/ma-proofbench, commit 31bab4c):
Authors: Lushi Pu, Weiming Zhang, Xinheng Xie, Zixuan Fu, Bingxiang He, Hongya Lyu,
Xin Li, Jie Zhou, Yudong Wang (MA-ProofBench).
The MIT License notice below applies to the adapted theorem statement and its documentation.

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

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination

/-!
# Partial fraction expansion of the squared cosecant

We prove the partial fraction expansion of `π² / sin² (π u)` for noninteger real `u`.
-/

public section

open Filter
open scoped Topology

namespace MathlibExt.Analysis.SpecialFunctions.TsumInvSqShiftEqPiSqDivSinSqWanted

private theorem tsum_eq_on_upperHalfPlane {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    (∑' n : ℤ, 1 / ((z + n) ^ 2)) =
      (Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * z) ^ 2 := by
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
    sin_pi_mul_ne_zero (UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩)
  have hlinear := (hasDerivAt_id z).const_mul (Real.pi : ℂ)
  have hcot : HasDerivAt (fun w : ℂ ↦ (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * w))
      (-((Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * z) ^ 2)) z := by
    convert (((Complex.hasDerivAt_cos _).comp z hlinear).div
      ((Complex.hasDerivAt_sin _).comp z hlinear) hsin).const_mul (Real.pi : ℂ) using 1
    · rfl
    · simp only [id_eq, Function.comp_apply, mul_one]
      field_simp [hsin]
      linear_combination Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * z)
  have hseries := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k := 1) (by decide) hz
  rw [iteratedDerivWithin_one, hcot.hasDerivWithinAt.derivWithin
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffWithinAt hz)] at hseries
  simpa using hseries.symm

/-- **Partial fraction expansion of $\pi^2/\sin^2(\pi u)$.** For every real number $u$ that is
not an integer,

$$\sum_{n \in \mathbb{Z}} \frac{1}{(u+n)^2} = \frac{\pi^2}{\sin^2(\pi u)}.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Sequences, series,
summability; Convergence and divergence of infinite limiting processes),
`benchmark/level2/ma_proofbench_l2_09.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem tsum_one_div_add_int_sq_eq_pi_sq_div_sin_sq
    (u : ℝ) (hu : u ∉ Set.range (fun n : ℤ => (n : ℝ))) :
    (∑' n : ℤ, 1 / ((u + n) ^ 2)) =
      (Real.pi ^ 2) / (Real.sin (Real.pi * u) ^ 2) := by
  have huc : (u : ℂ) ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    exact hu ⟨n, by exact_mod_cast hn⟩
  -- Approach the real axis along a vertical line, where the real summands dominate in norm.
  let z (t : ℝ) : ℂ := (u : ℂ) + (t : ℂ) * Complex.I
  have hz : Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 (u : ℂ)) := by
    have hc : Continuous z := by fun_prop
    simpa [z] using (hc.continuousAt (x := 0)).continuousWithinAt.tendsto
  have hterm (n : ℤ) : ContinuousAt (fun w : ℂ ↦ 1 / ((w + n) ^ 2)) (u : ℂ) :=
    continuousAt_const.div (by fun_prop)
      (pow_ne_zero _ (Complex.integerComplement_add_ne_zero huc n))
  have hsum : Tendsto (fun t ↦ ∑' n : ℤ, 1 / ((z t + n) ^ 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (∑' n : ℤ, 1 / (((u : ℂ) + n) ^ 2))) := by
    have hbound : Summable fun n : ℤ ↦ ‖1 / (((u : ℂ) + n) ^ 2)‖ := by
      simpa [one_div] using
        (EisensteinSeries.linear_right_summable (u : ℂ) 1 (k := 2) (by decide)).norm
    refine tendsto_tsum_of_dominated_convergence hbound (fun n ↦ (hterm n).tendsto.comp hz)
      (Eventually.of_forall fun t n ↦ ?_)
    have hle : ‖(u : ℂ) + n‖ ≤ ‖z t + n‖ := by
      simpa [z, ← Complex.ofReal_intCast, ← Complex.ofReal_add, Complex.norm_real] using
        Complex.abs_re_le_norm (z t + n)
    simp only [norm_div, norm_one, norm_pow]
    exact one_div_le_one_div_of_le
      (pow_pos (norm_pos_iff.mpr (Complex.integerComplement_add_ne_zero huc n)) _)
      (pow_le_pow_left₀ (norm_nonneg _) hle _)
  have hratio : ContinuousAt
      (fun w : ℂ ↦ (Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * w) ^ 2) (u : ℂ) :=
    continuousAt_const.div (by fun_prop) (pow_ne_zero _ (sin_pi_mul_ne_zero huc))
  have heq : (fun t ↦ ∑' n : ℤ, 1 / ((z t + n) ^ 2)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t ↦ (Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * z t) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact tsum_eq_on_upperHalfPlane (z := z t) (by simpa [z, UpperHalfPlane.upperHalfPlaneSet])
  have h := tendsto_nhds_unique hsum ((hratio.tendsto.comp hz).congr' heq.symm)
  rw [← Complex.ofReal_inj, Complex.ofReal_tsum]
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_add,
    Complex.ofReal_intCast, Complex.ofReal_sin, Complex.ofReal_mul] using h

end MathlibExt.Analysis.SpecialFunctions.TsumInvSqShiftEqPiSqDivSinSqWanted
