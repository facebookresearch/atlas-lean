/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_20.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the statement of
`norm_le_norm_cayley_of_upperHalfPlane_bounded_vanishing_at_I` (the source's
`ma_proofbench_l1_20`, renamed and placed in a namespace) and the informal problem statement
that its docstring restates.
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
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Complex.Schwarz
import MathlibExt.Analysis.Complex.DiskToUpperHalfPlaneCayley

/-!
# Schwarz lemma on the upper half-plane

Let `F : ℂ → ℂ` be holomorphic on the upper half-plane `ℍ = {z | 0 < z.im}`, with `‖F z‖ ≤ 1`
for `z ∈ ℍ` and `F I = 0`. Then `‖F z‖ ≤ ‖(z - I) / (z + I)‖` for every `z ∈ ℍ`.

The proof transports the Schwarz lemma from the unit disc. The Cayley map
`φ u = I * (1 - u) / (1 + u)` sends the open unit disc bijectively onto `ℍ`
(`DiskToUpperHalfPlaneCayleyWanted.bijOn_cayley_ball_upperHalfPlane`) and `φ 0 = I`, so `F ∘ φ`
is holomorphic on the unit disc, maps it into the closed unit disc and vanishes at `0`. The
Schwarz lemma (`Complex.norm_le_norm_of_mapsTo_ball`) gives `‖F (φ u)‖ ≤ ‖u‖`, and
`(φ u - I) / (φ u + I) = -u`.

## Main results

* `norm_le_norm_cayley_of_upperHalfPlane_bounded_vanishing_at_I`: the Schwarz lemma on the upper
  half-plane, for a function vanishing at `I`.
-/

namespace MathlibExt.Analysis.Complex.UpperHalfPlaneSchwarzLemmaWanted

/-- **Schwarz lemma on the upper half-plane.** Let
$\mathbb{H}=\{z\in\mathbb{C} : \mathrm{Im}\,z>0\}$ be the upper half-plane, and let $F$ be a
complex function that is holomorphic on $\mathbb{H}$, satisfies $|F(z)|\le 1$ for every
$z\in\mathbb{H}$, and vanishes at $i$. Then for every $z\in\mathbb{H}$,
$$|F(z)|\le\left|\frac{z-i}{z+i}\right|.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; Geometric function theory), `benchmark/level1/ma_proofbench_l1_20.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem norm_le_norm_cayley_of_upperHalfPlane_bounded_vanishing_at_I (F : ℂ → ℂ)
    (hHolo : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hBound : ∀ z, 0 < z.im → norm (F z) ≤ 1)
    (hFi : F Complex.I = 0) :
    ∀ z : ℂ, 0 < z.im →
      norm (F z) ≤ norm ((z - Complex.I) / (z + Complex.I)) := by
  intro z hz
  -- The Cayley map `φ` sends the open unit disc bijectively onto the upper half-plane.
  set φ : ℂ → ℂ := fun u => Complex.I * (1 - u) / (1 + u)
  have hφ := DiskToUpperHalfPlaneCayleyWanted.bijOn_cayley_ball_upperHalfPlane φ rfl
  have hden {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) 1) : 1 + u ≠ 0 := by
    intro h
    rw [add_eq_zero_iff_eq_neg'] at h
    simp [h] at hu
  have hφd : DifferentiableOn ℂ φ (Metric.ball 0 1) := fun u hu =>
    (((differentiableAt_const _).mul ((differentiableAt_const _).sub differentiableAt_id)).div
      ((differentiableAt_const _).add differentiableAt_id) (hden hu)).differentiableWithinAt
  -- Write `z = φ u` with `‖u‖ < 1`.
  obtain ⟨u, hu, rfl⟩ := hφ.surjOn hz
  -- `F ∘ φ` maps the unit disc into the closed unit disc and vanishes at `0`, as `φ 0 = I`.
  have hG : ‖(F ∘ φ) u‖ ≤ ‖u‖ :=
    Complex.norm_le_norm_of_mapsTo_ball (hHolo.comp hφd hφ.mapsTo)
      (fun v hv => mem_closedBall_zero_iff.mpr (hBound _ (hφ.mapsTo hv)))
      (by simp [φ, hFi]) (mem_ball_zero_iff.mp hu)
  -- The point `(φ u - I) / (φ u + I)` is `-u`.
  have hne : φ u + Complex.I ≠ 0 := fun h => by
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
    linarith [show 0 < (φ u).im from hz]
  have key : (φ u - Complex.I) / (φ u + Complex.I) = -u := by
    rw [div_eq_iff hne]
    simp only [φ]
    field_simp [hden hu]
    ring
  rw [key, norm_neg]
  exact hG

end MathlibExt.Analysis.Complex.UpperHalfPlaneSchwarzLemmaWanted
