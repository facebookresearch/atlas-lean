/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Algebra.Group.ContinuousDiv
public import Mathlib.Topology.MetricSpace.Isometry
public import MathlibExt.Combinatorics.CleanLatticeParallelogram

/-!
# Point reflection in a parallelogram

Reflection through the center preserves the parallelogram and exchanges its two antidiagonal
triangles.
-/

namespace MetaMathlibExt

private theorem image_sub_latticeParallelogram (u v : ℝ × ℝ) :
    (fun p => u + v - p) '' latticeParallelogram u v = latticeParallelogram u v := by
  have hP : Set.MapsTo (fun p => u + v - p) (latticeParallelogram u v)
      (latticeParallelogram u v) := by
    rintro _ ⟨s, t, hs₀, hs₁, ht₀, ht₁, rfl⟩
    refine ⟨1 - s, 1 - t, sub_nonneg.mpr hs₁, sub_le_self _ hs₀,
      sub_nonneg.mpr ht₁, sub_le_self _ ht₀, ?_⟩
    change u + v - (s • u + t • v) = _
    simp only [sub_smul, one_smul]
    abel
  refine Set.Subset.antisymm hP.image_subset fun p hp => ⟨u + v - p, hP hp, ?_⟩
  exact sub_sub_cancel _ _

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
  have hP_image : r '' latticeParallelogram u v = latticeParallelogram u v :=
    image_sub_latticeParallelogram u v
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

set_option linter.unusedVariables false in
/-- **The point reflection symmetry of $P_{a,n}$.** Let $a$ and $n$ be natural numbers with
$1 \le a < n$ and $\gcd(a, n) = 1$, let $P_{a,n} \subseteq \mathbb{R}^2$ be the parallelogram
with vertices $(0, 0)$, $(1, 0)$, $(a, n)$, $(a + 1, n)$, and let
$S : \mathbb{R}^2 \to \mathbb{R}^2$ be $S(x, y) = (a + 1 - x, n - y)$. Then $S(P_{a,n}) = P_{a,n}$,
and $S$ is an isometry of $\mathbb{R}^2$ for the maximum distance
$d((x, y), (x', y')) = \max(|x - x'|, |y - y'|)$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 4 (`integers-2026-A10-lem-4`). -/
public theorem stdCleanParallelogram_symmetry {a n : ℕ} (ha : 1 ≤ a) (han : a < n)
    (hcop : Nat.Coprime a n) :
    (fun p : ℝ × ℝ => ((a + 1 : ℝ) - p.1, (n : ℝ) - p.2)) '' stdCleanParallelogram a n =
        stdCleanParallelogram a n ∧
      Isometry fun p : ℝ × ℝ => ((a + 1 : ℝ) - p.1, (n : ℝ) - p.2) := by
  refine ⟨?_, ?_⟩
  · have hcorner : (1, 0) + ((a : ℝ), (n : ℝ)) = ((a + 1 : ℝ), (n : ℝ)) := by
      ext <;> simp [add_comm]
    change (fun p => ((a + 1 : ℝ), (n : ℝ)) - p) '' _ = _
    simpa only [stdCleanParallelogram, hcorner] using image_sub_latticeParallelogram (1, 0) (a, n)
  · apply Isometry.of_dist_eq
    intro p q
    simp only [Prod.dist_eq, Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm]

end MetaMathlibExt
