/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_71.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the theorem statement.
Authors: Lushi Pu, Weiming Zhang, Xinheng Xie, Zixuan Fu, Bingxiang He, Hongya Lyu, Xin Li,
Jie Zhou and Yudong Wang.
Licensed under the MIT License.
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

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import MathlibExt.Analysis.Complex.GreatPicard
import MathlibExt.Analysis.Complex.SchwarzReflection

/-!
# Surjectivity of upper half-plane self-maps

A nonconstant holomorphic self-map that extends continuously to the real axis
with real boundary values maps the open upper half-plane onto itself.
-/

open Set
open MathlibExt.Analysis.Complex.GreatPicardWanted

namespace MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapSurjectiveWanted

/-- **Surjectivity for half-plane self-maps that are real on the real axis.** Let
$\mathbb{C}_{+} = \{z \in \mathbb{C} : \operatorname{Im} z > 0\}$ be the open upper half-plane and
$\overline{\mathbb{C}_{+}} = \{z \in \mathbb{C} : \operatorname{Im} z \ge 0\}$ the closed one. Let
$f : \mathbb{C} \to \mathbb{C}$ be continuous on $\overline{\mathbb{C}_{+}}$ with
$f(\overline{\mathbb{C}_{+}}) \subseteq \overline{\mathbb{C}_{+}}$, suppose $f(x)$ is real for
every real $x$, and suppose $f$ is holomorphic on $\mathbb{C}_{+}$ and not constant on
$\mathbb{C}_{+}$. Then $f(\mathbb{C}_{+}) = \mathbb{C}_{+}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Geometric function theory), `benchmark/level2/ma_proofbench_l2_71.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem image_upperHalfPlane_eq_of_real_on_real
  (f : ℂ → ℂ)
  (hcont : ContinuousOn f {z : ℂ | 0 ≤ z.im})
  (hupper : ∀ z : ℂ, 0 ≤ z.im → 0 ≤ (f z).im)
  (hreal : ∀ x : ℝ, (f x).im = 0)
  (hhol : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
  (hnconst : ¬ ∃ c : ℂ, ∀ z : ℂ, 0 < z.im → f z = c) :
  f '' {z : ℂ | 0 < z.im} = {w : ℂ | 0 < w.im} := by
  have haxis (z : ℂ) (hz : z.im = 0) : (f z).im = 0 := by
    have heq : (z.re : ℂ) = z := Complex.ext rfl (by simpa using hz.symm)
    exact heq ▸ hreal z.re
  obtain ⟨g, hg, hagree, hconj⟩ := MetaMathlibExt.schwarz_reflection f hhol hcont haxis
  have hnc : ¬ ∃ c, ∀ z, g z = c := by
    rintro ⟨c, hc⟩
    exact hnconst ⟨c, fun z hz ↦ (hagree z hz.le).symm.trans (hc z)⟩
  have himage : g '' {z : ℂ | 0 < z.im} = f '' {z : ℂ | 0 < z.im} :=
    Set.EqOn.image_eq (fun z (hz : 0 < z.im) ↦ hagree z hz.le)
  rw [← himage]
  have hnonneg (z : ℂ) (hz : 0 ≤ z.im) : 0 ≤ (g z).im := hagree z hz ▸ hupper z hz
  apply Subset.antisymm
  · -- The open image lies in the interior of the closed upper half-plane.
    have hopen := (hg.analyticOnNhd isOpen_univ).is_constant_or_isOpenMap.resolve_left hnc
    conv_rhs => rw [← Complex.interior_setOfPred_le_im]
    apply interior_maximal _ (hopen _ (isOpen_lt continuous_const Complex.continuous_im))
    rintro _ ⟨z, hz, rfl⟩
    exact hnonneg z (le_of_lt hz)
  · intro w (hw : 0 < w.im)
    by_contra hmiss
    have homit (z : ℂ) : g z ≠ w := by
      intro heq
      by_cases hz : 0 < z.im
      · exact hmiss ⟨z, hz, heq⟩
      · have h := hnonneg (star z) (by simpa [Complex.star_def] using le_of_not_gt hz)
        rw [hconj, heq, Complex.star_def, Complex.conj_im] at h
        exact (not_le_of_gt hw) (neg_nonneg.mp h)
    have homit' (z : ℂ) : g z ≠ star w := by
      intro heq
      exact homit (star z) (by rw [hconj, heq, star_star])
    have heq : w = star w := littlePicard (differentiableOn_univ.mp hg) hnc homit homit'
    exact hw.ne' (Complex.conj_eq_iff_im.mp heq.symm)

end MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapSurjectiveWanted
