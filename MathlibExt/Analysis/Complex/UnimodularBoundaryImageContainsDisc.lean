/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

The theorem statement is adapted from `benchmark/level1/ma_proofbench_l1_25.lean` in
openbmb/ma-proofbench at commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, with the added
connectedness hypothesis described in the docstring.
Copyright (c) 2026 OpenBMB
Authors: L. Pu et al.
Licensed under the MIT License:

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

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.OpenMapping

/-!
# The image of a holomorphic function with unimodular boundary values

The open mapping theorem and the maximum modulus principle put the image of the open unit disc
inside the disc. Compactness of the closed disc and the boundary condition then make this image
relatively closed in the open disc.
-/

public section

open Metric Set

namespace MathlibExt.Analysis.Complex.UnimodularBoundaryImageContainsDiscWanted

/-- **Nonconstant holomorphic functions of modulus one on the unit circle cover the unit disc.**
Let $U\subseteq\mathbb{C}$ be a connected open set containing the closed unit disc
$\{z:|z|\le 1\}$, and let $f:\mathbb{C}\to\mathbb{C}$ be holomorphic on $U$ and non-constant on
$U$. If $|f(z)|=1$ whenever $|z|=1$, then every $w$ with $|w|<1$ is $f(z)$ for some $z\in U$; that
is, $f(U)$ contains the open unit disc.

The connectedness of $U$ is added to the source statement, which asks only for an open set: for
$U=\{z:|z|<2\}\cup\{z:|z-10|<1\}$, with $f=1$ on the first disc and $f(z)=z$ on the second, $f$
is non-constant and holomorphic on $U$ and has modulus one on the unit circle, but $f(U)$ does not
contain the open unit disc.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; General properties of functions of one complex variable),
`benchmark/level1/ma_proofbench_l1_25.lean` at openbmb/ma-proofbench@31bab4c, with the change
above.
-/
theorem ball_subset_image_of_norm_eq_one_on_sphere {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUconn : IsPreconnected U)
    (hclosed : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (hf : DifferentiableOn ℂ f U)
    (hnonconst : ∃ z₁ ∈ U, ∃ z₂ ∈ U, f z₁ ≠ f z₂)
    (hboundary : ∀ z, z ∈ Metric.sphere (0 : ℂ) 1 → ‖f z‖ = 1) :
    Metric.ball (0 : ℂ) 1 ⊆ f '' U := by
  let D := ball (0 : ℂ) 1
  have hDU : D ⊆ U := ball_subset_closedBall.trans hclosed
  obtain hconst | hopen := (hf.analyticOnNhd hU).is_constant_or_isOpen hUconn
  · obtain ⟨c, hc⟩ := hconst
    obtain ⟨x, hx, y, hy, hxy⟩ := hnonconst
    exact (hxy ((hc x hx).trans (hc y hy).symm)).elim
  have hopenD := hopen D hDU isOpen_ball
  have hbound : f '' D ⊆ closedBall 0 1 := by
    rintro _ ⟨z, hz, rfl⟩
    apply mem_closedBall_zero_iff.mpr
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hf.diffContOnCl_ball hclosed) (fun ζ hζ ↦ (hboundary ζ (frontier_ball_subset_sphere hζ)).le)
      (subset_closure hz)
  have hinto : f '' D ⊆ D := by
    simpa only [interior_closedBall _ one_ne_zero] using hopenD.subset_interior_iff.mpr hbound
  refine Subset.trans ?_ (image_mono hDU)
  apply (convex_ball (0 : ℂ) 1).isPreconnected.subset_of_closure_inter_subset hopenD
  · have hmem : f 0 ∈ f '' D := mem_image_of_mem f (mem_ball_self zero_lt_one)
    exact ⟨f 0, hinto hmem, hmem⟩
  · rintro w ⟨hw, hwD⟩
    have hclosedImage := ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn
      (hf.continuousOn.mono hclosed)).isClosed
    obtain ⟨z, hz, rfl⟩ := closure_minimal (image_mono ball_subset_closedBall) hclosedImage hw
    rw [← ball_union_sphere] at hz
    rcases hz with hz | hz
    · exact mem_image_of_mem f hz
    · exact ((mem_ball_zero_iff.mp hwD).ne (hboundary z hz)).elim

end MathlibExt.Analysis.Complex.UnimodularBoundaryImageContainsDiscWanted
