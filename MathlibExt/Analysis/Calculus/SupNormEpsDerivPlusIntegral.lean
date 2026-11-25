/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

The theorem statement in `benchmark/level2/ma_proofbench_l2_49.lean` (openbmb/ma-proofbench,
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029).
Copyright (c) 2026 OpenBMB
Licensed under the MIT License.
Authors: L. Pu et al.

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

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Sup norm bounds on the unit interval

Average the mean value estimate on a subinterval of length `min ε 1` containing the point
where the function is evaluated.
-/

namespace MathlibExt.Analysis.Calculus.SupNormEpsDerivPlusIntegralWanted

open Set MeasureTheory

/-- The supremum of the ordinary derivative norms also bounds the one-sided derivative norms
at the endpoints, by continuity from the interior. -/
private theorem norm_derivWithin_le_sSup {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc 0 1))
    {x : ℝ} (hx : x ∈ Icc 0 1) :
    ‖derivWithin f (Icc 0 1) x‖ ≤ sSup ((fun y => ‖deriv f y‖) '' Icc 0 1) := by
  have hcont := (hf.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl).norm
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hcont
  have hbdd : BddAbove ((fun y => ‖deriv f y‖) '' Icc 0 1) := by
    refine ⟨max B 0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    change ‖deriv f y‖ ≤ max B 0
    by_cases hd : DifferentiableAt ℝ f y
    · rw [← hd.derivWithin (uniqueDiffOn_Icc_zero_one y hy)]
      exact (hB (mem_image_of_mem _ hy)).trans (le_max_left ..)
    · simp [deriv_zero_of_not_differentiableAt hd]
  have hclosure := closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)
  apply le_on_closure (s := Ioo 0 1) (f := fun y => ‖derivWithin f (Icc 0 1) y‖)
    (g := fun _ => _) ?_ (by rwa [hclosure]) continuousOn_const (by rwa [hclosure])
  intro y hy
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
  exact le_csSup hbdd (mem_image_of_mem _ (Ioo_subset_Icc_self hy))

/-- **Sup norm on $[0,1]$ bounded by the derivative and the $L^1$ norm.** For every
$\varepsilon > 0$ there is a constant $C_\varepsilon > 0$ such that every function
$f : \mathbb{R} \to \mathbb{R}$ that is continuously differentiable on $[0,1]$ satisfies
$$\sup_{x \in [0,1]} |f(x)| \le
\varepsilon \sup_{x \in [0,1]} |f'(x)| + C_\varepsilon \int_0^1 |f(x)|\,dx.$$

At $x = 0$ and $x = 1$, $f'(x)$ is the two-sided derivative of $f$ on $\mathbb{R}$, taken to be $0$
where it does not exist; this does not change the supremum.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Inequalities
in real analysis), `benchmark/level2/ma_proofbench_l2_49.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_const_sSup_norm_le_mul_sSup_norm_deriv_add_mul_integral :
    ∀ ε > 0, ∃ Cε > 0, ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 1 f (Set.Icc (0 : ℝ) 1) →
      sSup (Set.image (fun x => ‖f x‖) (Set.Icc (0 : ℝ) 1))
        ≤ ε * sSup (Set.image (fun x => ‖deriv f x‖) (Set.Icc (0 : ℝ) 1))
            + Cε * ∫ x in (0 : ℝ)..1, ‖f x‖ := by
  intro ε hε
  let r := min ε 1
  have hr : 0 < r := lt_min hε zero_lt_one
  refine ⟨r⁻¹, inv_pos.mpr hr, ?_⟩
  intro f hf
  let M := sSup ((fun y => ‖deriv f y‖) '' Icc 0 1)
  have hderiv (y : ℝ) (hy : y ∈ Icc 0 1) : ‖derivWithin f (Icc 0 1) y‖ ≤ M :=
    norm_derivWithin_le_sSup hf hy
  apply csSup_le ((nonempty_Icc.mpr zero_le_one).image _)
  rintro _ ⟨x, hx, rfl⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans (hderiv x hx)
  -- Slide the interval to the left if starting it at x would cross 1.
  let a := min x (1 - r)
  have ha : 0 ≤ a := le_min hx.1 (sub_nonneg.mpr (min_le_right ε 1))
  have hab : a ≤ a + r := le_add_of_nonneg_right hr.le
  have hb : a + r ≤ 1 := (le_sub_iff_add_le).mp (min_le_right ..)
  have hx' : x ∈ Icc a (a + r) := by
    refine ⟨min_le_left .., ?_⟩
    rw [show a + r = min (x + r) 1 by simp [a, ← min_add_add_right]]
    exact le_min (le_add_of_nonneg_right hr.le) hx.2
  have hsub : Icc a (a + r) ⊆ Icc 0 1 := Icc_subset_Icc ha hb
  have hpoint (y : ℝ) (hy : y ∈ Icc a (a + r)) : ‖f x‖ - ε * M ≤ ‖f y‖ := by
    have hdist : ‖x - y‖ ≤ r := by
      simpa only [dist_eq_norm, add_sub_cancel_left] using Real.dist_le_of_mem_Icc hx' hy
    apply sub_le_comm.mp
    calc
      ‖f x‖ - ‖f y‖ ≤ ‖f x - f y‖ := norm_sub_norm_le ..
      _ ≤ M * ‖x - y‖ := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_derivWithin_le
        (hf.differentiableOn one_ne_zero) hderiv (hsub hy) hx
      _ ≤ M * ε := mul_le_mul_of_nonneg_left (hdist.trans (min_le_left ..)) hM
      _ = ε * M := mul_comm ..
  have hsmall := (hf.continuousOn.norm.mono hsub).intervalIntegrable_of_Icc (μ := volume) hab
  have havg := intervalIntegral.integral_mono_on hab intervalIntegrable_const hsmall hpoint
  have hwhole := intervalIntegral.integral_mono_interval ha hab hb
    (Filter.Eventually.of_forall fun y => norm_nonneg (f y))
    (hf.continuousOn.norm.intervalIntegrable_of_Icc (μ := volume) zero_le_one)
  apply sub_le_iff_le_add'.mp
  apply (le_inv_mul_iff₀ hr).mpr
  simpa only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul] using
    havg.trans hwhole

end MathlibExt.Analysis.Calculus.SupNormEpsDerivPlusIntegralWanted
