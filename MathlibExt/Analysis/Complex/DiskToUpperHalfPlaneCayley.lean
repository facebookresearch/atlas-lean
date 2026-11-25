/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_63.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the statement of
`bijOn_cayley_ball_upperHalfPlane`.
Authors: L. Pu et al. (MA-ProofBench)
MIT License

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

public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The Cayley map from the unit disk to the upper half-plane

Solving `w = I * (1 - z) / (1 + z)` for `z` gives `(I - w) / (I + w)`. For `w` in the
upper half-plane, the numerator has smaller norm than the denominator.
-/

open Complex

namespace MathlibExt.Analysis.Complex.DiskToUpperHalfPlaneCayleyWanted

/-- **A Möbius map from the unit disk onto the upper half-plane.** The function
$\phi(z) = i\,\frac{1-z}{1+z}$ maps the open unit disk $D = \{z \in \mathbb{C} : |z| < 1\}$
bijectively onto the upper half-plane $U = \{z \in \mathbb{C} : \operatorname{Im} z > 0\}$: it
maps $D$ into $U$, it is injective on $D$, and every point of $U$ is $\phi(z)$ for some $z \in D$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; Geometric function theory), `benchmark/level1/ma_proofbench_l1_63.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem bijOn_cayley_ball_upperHalfPlane
    (φ : ℂ → ℂ) (hφ : φ = fun z : ℂ => Complex.I * (1 - z) / (1 + z)) :
    Set.BijOn φ (Metric.ball (0 : ℂ) 1) {w : ℂ | 0 < w.im} := by
  subst φ
  have denom_ne {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) : 1 + z ≠ 0 :=
    UnitDisc.one_add_coe_ne_zero ⟨z, hz⟩
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    change 0 < (I * (1 - z) / (1 + z)).im
    rw [div_im, ← sub_div]
    refine div_pos ?_ (normSq_pos.mpr (denom_ne hz))
    have hsq : normSq z < 1 := UnitDisc.normSq_lt_one ⟨z, hz⟩
    rw [normSq_apply] at hsq
    simp only [I_mul_re, I_mul_im, sub_re, sub_im, add_re, add_im, one_re, one_im,
      zero_sub, neg_neg, zero_add]
    nlinarith
  · intro x hx y hy h
    change I * (1 - x) / (1 + x) = I * (1 - y) / (1 + y) at h
    rw [div_eq_div_iff (denom_ne hx) (denom_ne hy), mul_assoc, mul_assoc,
      mul_right_inj' I_ne_zero] at h
    linear_combination -h / 2
  · intro w hw
    change 0 < w.im at hw
    have hlt : ‖I - w‖ < ‖I + w‖ := by
      rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
        normSq_sub, normSq_add]
      simp only [I_mul_re, conj_im, neg_neg]
      linarith
    have hpos := (norm_nonneg _).trans_lt hlt
    have hz : (I - w) / (I + w) ∈ Metric.ball (0 : ℂ) 1 := by
      rwa [mem_ball_zero_iff, norm_div, div_lt_one hpos]
    refine ⟨_, hz, ?_⟩
    apply (div_eq_iff (denom_ne hz)).2
    field_simp [norm_pos_iff.mp hpos]
    ring

end MathlibExt.Analysis.Complex.DiskToUpperHalfPlaneCayleyWanted
