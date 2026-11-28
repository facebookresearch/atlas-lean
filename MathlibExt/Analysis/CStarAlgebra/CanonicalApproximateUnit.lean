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

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Order.Filter.Finite

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The computed canonical C-star approximate unit on compact coefficient ranges

Use the existing positive-contraction approximate-unit filter under the
actual canonical spectral order. Its original pointwise multiplication
limit and contraction bound become uniform on every compact set by a
finite metric cover. This applies to arbitrary nonunital and zero algebras
without countability or a supplied approximate-unit model.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Topology

namespace CStarAlgebra

noncomputable section

universe uA

variable (A : Type uA) [NonUnitalCStarAlgebra A]

/-- **Positive contractive approximate-unit filter.** Let `A` be a nonunital complex C*-algebra. This is
the canonical filter of positive contractions in `A`, using spectral order, along which
multiplication on either side converges to the identity. -/
def canonicalApproximateUnit : Filter A := by
  let _ : PartialOrder A := spectralOrder A
  let _ : StarOrderedRing A := spectralOrderedRing A
  exact approximateUnit A

/-- **Properness of the approximate-unit filter.** Let `A` be a nonunital complex C*-algebra. Its
canonical positive contractive approximate-unit filter is proper, including when `A` is the zero
algebra. -/
theorem canonicalApproximateUnit_neBot : (canonicalApproximateUnit A).NeBot := by
  let _ : PartialOrder A := spectralOrder A
  let _ : StarOrderedRing A := spectralOrderedRing A
  change (approximateUnit A).NeBot
  exact (increasingApproximateUnit A).neBot

/-- **Approximate-unit elements are contractions.** Let `A` be a nonunital complex C*-algebra. Along the
canonical positive contractive approximate-unit filter, `‖a‖ ≤ 1` eventually. -/
theorem canonicalApproximateUnit_eventually_norm_le_one :
    ∀ᶠ a in canonicalApproximateUnit A, ‖a‖ ≤ 1 := by
  let _ : PartialOrder A := spectralOrder A
  let _ : StarOrderedRing A := spectralOrderedRing A
  exact (increasingApproximateUnit A).eventually_norm

/-- **Approximate unit acts on the left.** Let `A` be a nonunital complex C*-algebra. For every fixed `x
∈ A`, `a x` tends to `x` in norm as `a` follows the canonical positive contractive approximate-unit
filter. -/
theorem tendsto_canonicalApproximateUnit_mul_right (x : A) :
    Tendsto (fun a : A => a * x) (canonicalApproximateUnit A) (𝓝 x) := by
  let _ : PartialOrder A := spectralOrder A
  let _ : StarOrderedRing A := spectralOrderedRing A
  exact (increasingApproximateUnit A).tendsto_mul_right x

/-- **Approximate unit acts on the right.** Let `A` be a nonunital complex C*-algebra. For every fixed
`x ∈ A`, `x a` tends to `x` in norm as `a` follows the canonical positive contractive
approximate-unit filter. -/
theorem tendsto_canonicalApproximateUnit_mul_left (x : A) :
    Tendsto (fun a : A => x * a) (canonicalApproximateUnit A) (𝓝 x) := by
  let _ : PartialOrder A := spectralOrder A
  let _ : StarOrderedRing A := spectralOrderedRing A
  exact (increasingApproximateUnit A).tendsto_mul_left x

/-- **Uniform approximate-unit convergence on compact sets.** Let `A` be a nonunital complex C*-algebra.
For every norm-compact `K ⊆ A` and `ε > 0`, eventually `‖a x - x‖ < ε` for all `x ∈ K` as `a`
follows the canonical positive contractive approximate-unit filter. -/
theorem canonicalApproximateUnit_eventually_compact_mul_sub_lt
    (K : Set A) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a in canonicalApproximateUnit A, ∀ x ∈ K, ‖a * x - x‖ < ε := by
  classical
  have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨t, hCover⟩ := hK.elim_finite_subcover
    (fun y : A => Metric.ball y (ε / 3)) (fun _ => Metric.isOpen_ball) (by
      intro x _hx
      exact mem_iUnion.mpr ⟨x, Metric.mem_ball_self hthird⟩)
  have hPoints : ∀ y ∈ t, ∀ᶠ a in canonicalApproximateUnit A, dist (a * y) y < ε / 3 := by
    intro y _hy
    exact Metric.tendsto_nhds.mp (tendsto_canonicalApproximateUnit_mul_right A y) (ε / 3) hthird
  have hAll : ∀ᶠ a in canonicalApproximateUnit A, ∀ y ∈ t, dist (a * y) y < ε / 3 :=
    (Filter.eventually_all_finset t).mpr hPoints
  filter_upwards [canonicalApproximateUnit_eventually_norm_le_one A, hAll] with a ha hAll
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (hCover hx)
  have hNear : dist x y < ε / 3 := Metric.mem_ball.mp hxy
  have hMul : dist (a * x) (a * y) ≤ dist x y := by
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub]
    exact (norm_mul_le a (x - y)).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (norm_nonneg (x - y)))
  have hResult : dist (a * x) x < ε := by
    calc
      dist (a * x) x ≤ dist (a * x) (a * y) + dist (a * y) x := dist_triangle _ _ _
      _ ≤ dist x y + (dist (a * y) y + dist y x) :=
        add_le_add hMul (dist_triangle _ _ _)
      _ < ε / 3 + (ε / 3 + ε / 3) :=
        add_lt_add hNear (add_lt_add (hAll y hyt) (by simpa only [dist_comm] using hNear))
      _ = ε := by ring
  simpa only [dist_eq_norm] using hResult

end

end CStarAlgebra
