/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Only the theorem statement (with its adapted docstring) is taken from
openbmb/ma-proofbench at commit 31bab4c78fd1b0c464e767d62e9202163d1e9029,
`benchmark/level1/ma_proofbench_l1_76.lean` (MA-ProofBench, L. Pu et al.,
arXiv:2606.13782). ATLAS renamed and namespaced the declaration, first recorded
it as a wanted statement, and now supplies an independent proof.

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

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

/-! # Opial's inequality on an interval -/

open MeasureTheory (volume)
open Set intervalIntegral

namespace MathlibExt.Analysis.Calculus.OpialTypeIntegralInequalityWanted

/-- **Opial's inequality with one boundary condition.** Let $\alpha \le \beta$ be real numbers and
let $f : \mathbb{R} \to \mathbb{R}$ be continuously differentiable on $[\alpha, \beta]$ with
$f(\alpha) = 0$. Then

$$\int_\alpha^\beta |f(x) f'(x)|\,dx \le \frac{\beta - \alpha}{2} \int_\alpha^\beta |f'(x)|^2\,dx.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Inequalities in
real analysis), `benchmark/level1/ma_proofbench_l1_76.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem integral_abs_mul_deriv_le_of_eq_zero_left {α β : ℝ} (hαβ : α ≤ β) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc α β))
    (hfa : f α = 0) :
    (∫ x in α..β, |f x * deriv f x|)
      ≤ ((β - α) / 2) * ∫ x in α..β, (|deriv f x| ^ 2) := by
  rcases hαβ.eq_or_lt with rfl | hlt
  · simp
  -- The within derivative is continuous up to the endpoints. The ordinary derivative
  -- agrees with it in the interior, which suffices for the interval integrals.
  let g : ℝ → ℝ := fun x => |derivWithin f (Icc α β) x|
  have hg : ContinuousOn g (Icc α β) :=
    (hf.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl).abs
  have hg_eq (x : ℝ) (hx : x ∈ Ioo α β) : |deriv f x| = g x := by
    dsimp [g]
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  let G : ℝ → ℝ := fun x => ∫ t in α..x, g t
  have hg_int := hg.intervalIntegrable_of_Icc (μ := volume) hlt.le
  have hG : ContinuousOn G (Icc α β) := by
    rw [← uIcc_of_le hlt.le] at hg ⊢
    exact continuousOn_primitive_interval (hg.integrableOn_compact isCompact_uIcc)
  have hG₀ : G α = 0 := integral_same
  have hbound (x : ℝ) (hx : x ∈ Icc α β) : |f x| ≤ G x := by
    have hsub : Icc α x ⊆ Icc α β := Icc_subset_Icc_right hx.2
    calc
      |f x| = |∫ t in α..x, deriv f t| := by
        rw [integral_deriv_of_contDiffOn_Icc (hf.mono hsub) hx.1, hfa, sub_zero]
      _ ≤ ∫ t in α..x, |deriv f t| := abs_integral_le_integral_abs hx.1
      _ = G x := integral_congr_Ioo_of_le hx.1 fun t ht =>
        hg_eq t ⟨ht.1, ht.2.trans_le hx.2⟩
  have hG' (x : ℝ) (hx : x ∈ Ioo α β) : HasDerivAt G (g x) x := by
    have hn := Icc_mem_nhds hx.1 hx.2
    apply integral_hasDerivAt_right
    · exact (hg.mono (Icc_subset_Icc_right hx.2.le)).intervalIntegrable_of_Icc hx.1.le
    · exact ⟨Icc α β, hn, hg.aestronglyMeasurable measurableSet_Icc⟩
    · exact (hg x (mem_Icc_of_Ioo hx)).continuousAt hn
  have hGg_int := (hG.mul hg).intervalIntegrable_of_Icc (μ := volume) hlt.le
  have hGg : (∫ x in α..β, G x * g x) = G β ^ 2 / 2 := by
    have hderiv (x : ℝ) (hx : x ∈ Ioo α β) :
        HasDerivAt (fun t => (1 / 2) * (G t * G t)) (G x * g x) x := by
      convert HasDerivAt.const_mul (1 / 2) ((hG' x hx).mul (hG' x hx)) using 1
      ring
    rw [integral_eq_sub_of_hasDerivAt_of_le hlt.le (continuousOn_const.mul (hG.mul hG))
      hderiv hGg_int]
    change (1 / 2) * (G β * G β) - (1 / 2) * (G α * G α) = G β ^ 2 / 2
    rw [hG₀]
    ring
  -- Cauchy–Schwarz against the constant function 1, written as an integral of a square.
  let L := β - α
  have hL : 0 < L := sub_pos.mpr hlt
  have hcs : G β ^ 2 ≤ L * ∫ x in α..β, g x ^ 2 := by
    have hsq : IntervalIntegrable (fun x => g x ^ 2) volume α β :=
      (hg.pow 2).intervalIntegrable_of_Icc hlt.le
    have hconst : IntervalIntegrable (fun _ : ℝ => G β ^ 2) volume α β := intervalIntegrable_const
    have hnonneg : 0 ≤ ∫ x in α..β, (L * g x - G β) ^ 2 :=
      integral_nonneg hlt.le fun x _ => sq_nonneg _
    have hexpand : (∫ x in α..β, (L * g x - G β) ^ 2) =
        L * (L * (∫ x in α..β, g x ^ 2) - G β ^ 2) := by
      calc
        _ = ∫ x in α..β, (L ^ 2 * g x ^ 2 - (2 * L * G β) * g x) + G β ^ 2 :=
          integral_congr fun x _ => by ring
        _ = _ := by
          rw [integral_add ((hsq.const_mul _).sub (hg_int.const_mul _)) hconst,
            integral_sub (hsq.const_mul _) (hg_int.const_mul _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            integral_const, smul_eq_mul]
          change L ^ 2 * (∫ x in α..β, g x ^ 2) - (2 * L * G β) * G β + L * G β ^ 2 = _
          ring
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (hexpand ▸ hnonneg) hL)
  calc
    (∫ x in α..β, |f x * deriv f x|) = ∫ x in α..β, |f x| * g x :=
      integral_congr_Ioo_of_le hlt.le fun x hx => by rw [abs_mul, hg_eq x hx]
    _ ≤ ∫ x in α..β, G x * g x :=
      integral_mono_on hlt.le ((hf.continuousOn.abs.mul hg).intervalIntegrable_of_Icc hlt.le)
        hGg_int fun x hx => mul_le_mul_of_nonneg_right (hbound x hx) (abs_nonneg _)
    _ = G β ^ 2 / 2 := hGg
    _ ≤ (L * ∫ x in α..β, g x ^ 2) / 2 := div_le_div_of_nonneg_right hcs (by norm_num)
    _ = (L / 2) * ∫ x in α..β, (|deriv f x| ^ 2) := by
      have heq : (∫ x in α..β, |deriv f x| ^ 2) = ∫ x in α..β, g x ^ 2 :=
        integral_congr_Ioo_of_le hlt.le fun x hx => by rw [hg_eq x hx]
      rw [heq]
      ring

end MathlibExt.Analysis.Calculus.OpialTypeIntegralInequalityWanted
