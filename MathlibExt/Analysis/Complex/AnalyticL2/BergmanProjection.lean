/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Complex.AnalyticL2.EvaluationBound
public import MathlibExt.Analysis.Complex.AnalyticL2.Closedness
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# The analytic L2 submodule and its Bergman projection

On any open planar set `G`, use scalar L2 for planar volume restricted to
`G`. Analytic representatives of two classes obey a uniform positive
L2 difference bound on every compact subset of `G`. Consequently the
analytic-representative submodule is closed and complete in the inherited
L2 norm.

The Bergman projection is the continuous complex-linear orthogonal
projection from that same L2 Hilbert space onto that same submodule.
The domain may be empty or unbounded; no bounded-domain, probability-measure
or finite-area hypothesis is introduced.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Metric Set

namespace AnalyticL2

/-- Every compact subset of an open planar domain has a positive uniform bound on analytic
representative differences in terms of L2 class differences.

```lean
theorem compact_local_bound (G : Set ℂ) (hG : IsOpen G) (K : Set ℂ)
    (hKG : K ⊆ G) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f h : Lp ℂ 2 (volume.restrict G)) (g k : ℂ → ℂ),
      AnalyticOn ℂ g G → AnalyticOn ℂ k G →
      (∀ᵐ z ∂volume.restrict G, f z = g z) →
      (∀ᵐ z ∂volume.restrict G, h z = k z) →
      ∀ z ∈ K, ‖g z - k z‖ ≤ C * ‖f - h‖
``` -/
theorem compact_local_bound (G : Set ℂ) (hG : IsOpen G) (K : Set ℂ)
    (hKG : K ⊆ G) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f h : Lp ℂ 2 (volume.restrict G)) (g k : ℂ → ℂ),
      AnalyticOn ℂ g G → AnalyticOn ℂ k G →
      (∀ᵐ z ∂volume.restrict G, f z = g z) →
      (∀ᵐ z ∂volume.restrict G, h z = k z) →
      ∀ z ∈ K, ‖g z - k z‖ ≤ C * ‖f - h‖ := by
  obtain ⟨r, hr, hInside⟩ := hK.exists_cthickening_subset_open hG hKG
  let C : ℝ := (Real.pi * r ^ 2) ^ (1 / 2 : ℝ) / (Real.pi * r ^ 2)
  have hVolume : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  refine ⟨C, div_pos (Real.rpow_pos_of_pos hVolume _) hVolume, ?_⟩
  intro f h g k hg hk hfg hhk z hz
  have hDifference : ∀ᵐ w ∂volume.restrict G, (f - h) w = (g - k) w := by
    filter_upwards [Lp.coeFn_sub f h, hfg, hhk] with w hw hfw hhw
    exact hw.trans (congrArg₂ (fun x y : ℂ => x - y) hfw hhw)
  have hDisk : closedBall z r ⊆ G :=
    (closedBall_subset_cthickening hz r).trans hInside
  simpa only [C, Pi.sub_apply] using
    norm_point_le G (g - k) (hg.sub hk) (f - h) hDifference z r hr hDisk

/-- The analytic-representative submodule is closed in scalar L2 of planar volume restricted to an
open domain.

```lean
theorem submodule_isClosed (G : Set ℂ) (hG : IsOpen G) :
    IsClosed (submodule G (volume.restrict G) : Set (Lp ℂ 2 (volume.restrict G)))
``` -/
theorem submodule_isClosed (G : Set ℂ) (hG : IsOpen G) :
    IsClosed (submodule G (volume.restrict G) : Set (Lp ℂ 2 (volume.restrict G))) :=
  isClosed_of_local_bound G hG (fun K hKG hK => compact_local_bound G hG K hKG hK)

/-- The analytic-representative submodule on an open domain is complete with the same inherited
restricted-volume L2 norm.

```lean
theorem completeSpace (G : Set ℂ) (hG : IsOpen G) :
    CompleteSpace (submodule G (volume.restrict G))
``` -/
theorem completeSpace (G : Set ℂ) (hG : IsOpen G) :
    CompleteSpace (submodule G (volume.restrict G)) :=
  (submodule_isClosed G hG).completeSpace_coe

/-- The continuous complex-linear orthogonal projection of restricted-volume L2 onto its closed
analytic-representative submodule. -/
def projection (G : Set ℂ) (hG : IsOpen G) :
    Lp ℂ 2 (volume.restrict G) →L[ℂ] submodule G (volume.restrict G) := by
  let : CompleteSpace (submodule G (volume.restrict G)) := completeSpace G hG
  exact Submodule.orthogonalProjectionOnto (𝕜 := ℂ) (E := Lp ℂ 2 (volume.restrict G))
    (submodule G (volume.restrict G))

end AnalyticL2

end
