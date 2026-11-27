/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_18.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029).
Copyright (c) 2026 OpenBMB.
Licensed under the MIT License below.
Authors: L. Pu et al.
Adapted portions: the theorem statement and its problem description.

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
public import Mathlib.Analysis.Complex.Schwarz
import MathlibExt.Analysis.Complex.HarmonicConjugateSimplyConnected

/-!
# Boundary distance for a normalized univalent map

The distance from zero to the boundary of the image of the unit disc is at most one.
Schwarz's lemma applied to the inverse bounds the radius of every disc centered at zero
that lies in the image.
-/

public section

open Function Metric Set
open scoped Topology

namespace MathlibExt.Analysis.Complex.UnivalentImageBoundaryDistLeOneWanted

/-- **The boundary of a normalized univalent image of the disc is within distance one of the
origin.** Let $D=\{z\in\mathbb{C}:|z|<1\}$ be the unit disk and suppose $f:D\to\mathbb{C}$ is an
injective holomorphic function with $f(0)=0$ and $f'(0)=1$. Let $\Omega=f(D)$ and let
$\partial\Omega$ be its boundary. Then
$\mathrm{dist}(0,\partial\Omega)=\inf\{|z|:z\in\partial\Omega\}\le 1$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Geometric function theory), `benchmark/level2/ma_proofbench_l2_18.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem infDist_zero_frontier_image_ball_le_one
  (f : ℂ → ℂ) (hf_holo : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
  (hf_inj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (hf0 : f 0 = 0) (hf'0 : deriv f 0 = 1) :
  Metric.infDist (0 : ℂ) (frontier (f '' (Metric.ball (0 : ℂ) 1))) ≤ 1 := by
  let D := ball (0 : ℂ) 1
  let Ω := f '' D
  let g := invFunOn f D
  have h0 : (0 : ℂ) ∈ D := mem_ball_self zero_lt_one
  have hleft : LeftInvOn g f D := hf_inj.leftInvOn_invFunOn
  have hg0 : g 0 = 0 := by simpa only [hf0] using hleft h0
  have hg (z : ℂ) (hz : z ∈ D) : DifferentiableAt ℂ g (f z) :=
    (Complex.analyticAt_invFunOn isOpen_ball hf_holo hf_inj hz).differentiableAt
  -- Differentiate the identity g ∘ f = id near zero.
  have hgf : g ∘ f =ᶠ[𝓝 0] id := Filter.eventually_of_mem (ball_mem_nhds _ zero_lt_one) hleft
  have hg'0 := hgf.deriv_eq (𝕜 := ℂ)
  rw [deriv_comp 0 (hg 0 h0) (hf_holo.differentiableAt (ball_mem_nhds _ zero_lt_one)),
    hf0, hf'0, mul_one, deriv_id] at hg'0
  have radius_le_one (r : ℝ) (hr : ball 0 r ⊆ Ω) : r ≤ 1 := by
    rcases le_or_gt r 0 with hrnonpos | hrpos
    · exact hrnonpos.trans zero_le_one
    · have hdiff : DifferentiableOn ℂ g (ball 0 r) := by
        intro w hw
        obtain ⟨z, hz, rfl⟩ := hr hw
        exact (hg z hz).differentiableWithinAt
      have hmaps : MapsTo g (ball 0 r) (closedBall (g 0) 1) := by
        rw [hg0]
        intro w hw
        exact ball_subset_closedBall (invFunOn_mem (hr hw))
      have h := Complex.norm_deriv_le_div_of_mapsTo_ball hdiff hmaps hrpos
      rw [hg'0, norm_one] at h
      simpa only [one_mul] using (le_div_iff₀ hrpos).mp h
  -- The image omits a point, so the distance to its complement is attained on the frontier.
  have hproper : Ω ≠ univ := by
    intro h
    have := radius_le_one 2 (h ▸ subset_univ _)
    norm_num at this
  have hmem : (0 : ℂ) ∈ Ω := ⟨0, h0, hf0⟩
  obtain ⟨w, hw, hdist⟩ := exists_mem_frontier_infDist_compl_eq_dist hmem hproper
  exact (infDist_le_dist_of_mem hw).trans
    (hdist ▸ radius_le_one _ ball_infDist_compl_subset)

end MathlibExt.Analysis.Complex.UnivalentImageBoundaryDistLeOneWanted
