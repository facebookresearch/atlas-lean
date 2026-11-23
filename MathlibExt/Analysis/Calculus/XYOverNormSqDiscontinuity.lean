/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_93.lean` (openbmb/ma-proofbench, commit 31bab4c).
The theorem statement is adapted from MA-ProofBench under the MIT License.
Authors: Lushi Pu, Weiming Zhang, Xinheng Xie, Zixuan Fu, Bingxiang He, Hongya Lyu, Xin Li,
Jie Zhou, Yudong Wang.

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

public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Discontinuity of `xy / (x² + y²)` at the origin

The denominator vanishes only at the origin. On the punctured diagonal the quotient is
constant with value `1 / 2`, whereas the prescribed value at the origin is zero.
-/

open Filter
open scoped Topology

public section

namespace MathlibExt.Analysis.Calculus.XYOverNormSqDiscontinuityWanted

/-- **The function $xy/(x^2+y^2)$ is discontinuous only at the origin.** Let
$f : \mathbb{R}^2 \to \mathbb{R}$ be given by $f(x,y) = \frac{xy}{x^2+y^2}$ for
$(x,y) \neq (0,0)$ and $f(0,0) = 0$. Then $f$ is continuous on $\mathbb{R}^2 \setminus \{(0,0)\}$
and is not continuous at $(0,0)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
several variables), `benchmark/level1/ma_proofbench_l1_93.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem continuousOn_compl_and_not_continuousAt_mul_div_sq_add_sq
    (f : (ℝ × ℝ) → ℝ)
    (hf : (∀ p : (ℝ × ℝ), p ≠ (0, 0) → f p = (p.1 * p.2) / (p.1 ^ (2 : ℕ) + p.2 ^ (2 : ℕ))) ∧
      (f (0, 0) = 0)) :
    ContinuousOn f ({(0, 0)}ᶜ) ∧ ¬ ContinuousAt f (0, 0) := by
  obtain ⟨hformula, hzero⟩ := hf
  constructor
  · refine (ContinuousOn.div (continuous_fst.mul continuous_snd).continuousOn
      ((continuous_fst.pow 2).add (continuous_snd.pow 2)).continuousOn ?_).congr ?_
    · intro p hp h
      obtain ⟨hx, hy⟩ := sq_add_sq_eq_zero.mp h
      exact hp (Prod.ext hx hy)
    · exact fun p hp => hformula p hp
  · intro hc
    have hdiag : ContinuousAt (fun t : ℝ => f (t, t)) 0 :=
      hc.comp₂ (g := id) (h := id) continuousAt_id continuousAt_id
    have hhalf : (fun t : ℝ => f (t, t)) =ᶠ[𝓝[≠] 0] fun _ => 1 / 2 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change t ≠ 0 at ht
      rw [hformula (t, t) (by simp [ht])]
      change t * t / (t ^ 2 + t ^ 2) = 1 / 2
      rw [← sq, ← mul_two, ← div_div, div_self (pow_ne_zero 2 ht)]
    have heq := tendsto_nhds_unique hdiag.continuousWithinAt.tendsto hhalf.tendsto
    norm_num [hzero] at heq

end MathlibExt.Analysis.Calculus.XYOverNormSqDiscontinuityWanted
