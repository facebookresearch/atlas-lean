/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Algebra.Group.ContinuousDiv
public import MathlibExt.Combinatorics.CleanLatticeParallelogram

/-!
# Point reflection in a parallelogram

Reflection through the center exchanges the two antidiagonal triangles inside the parallelogram.
-/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **Point reflection between the two triangles of a parallelogram.** Let $u$ and $v$ be
linearly independent vectors in $\mathbb{R}^2$ and let $P$ be the parallelogram they span. The map
$p \mapsto u + v - p$ is a bijection from the set of points of the triangle
$\operatorname{conv}\{0, u, v\}$ that lie in the interior of $P$ onto the set of points of the
triangle $\operatorname{conv}\{u, v, u + v\}$ that lie in the interior of $P$.

The map sends $s u + t v$ to $(1 - s) u + (1 - t) v$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 1 (`integers-2026-A10-lem-1`). -/
public theorem antidiagonal_triangle_bijOn {u v : ℝ × ℝ}
    (huv : LinearIndependent ℝ ![u, v]) :
    Set.BijOn (fun p => u + v - p)
      (convexHull ℝ {0, u, v} ∩ interior (latticeParallelogram u v))
      (convexHull ℝ {u, v, u + v} ∩ interior (latticeParallelogram u v)) := by
  let r := Homeomorph.subLeft (u + v)
  have hP : Set.MapsTo r (latticeParallelogram u v) (latticeParallelogram u v) := by
    rintro _ ⟨s, t, hs₀, hs₁, ht₀, ht₁, rfl⟩
    refine ⟨1 - s, 1 - t, sub_nonneg.mpr hs₁, sub_le_self _ hs₀,
      sub_nonneg.mpr ht₁, sub_le_self _ ht₀, ?_⟩
    change u + v - (s • u + t • v) = _
    simp only [sub_smul, one_smul]
    abel
  have hP_image : r '' latticeParallelogram u v = latticeParallelogram u v := by
    refine Set.Subset.antisymm hP.image_subset fun p hp => ⟨r p, hP hp, ?_⟩
    exact sub_sub_cancel _ _
  have hT : r '' convexHull ℝ {0, u, v} = convexHull ℝ {u, v, u + v} := by
    change (AffineEquiv.constVSub ℝ (u + v)).toAffineMap '' _ = _
    rw [AffineMap.image_convexHull]
    congr 1
    change (fun p => u + v - p) '' {0, u, v} = _
    ext p
    simp [or_comm, or_assoc]
  apply r.toEquiv.image_eq_iff_bijOn.mp
  change r '' _ = _
  rw [Set.image_inter r.injective, r.image_interior, hP_image, hT]

end MetaMathlibExt
