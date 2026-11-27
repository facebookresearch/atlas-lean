/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MetaMathlibExt

/-- **Monge's three-circle theorem, algebraic form.** Let $V$ be a real vector space, let
$c_1, c_2, c_3 \in V$, and let $r_1, r_2, r_3$ be pairwise distinct real numbers. Then the three
points $(r_1 - r_2)^{-1}(r_1 c_2 - r_2 c_1)$, $(r_2 - r_3)^{-1}(r_2 c_3 - r_3 c_2)$ and
$(r_1 - r_3)^{-1}(r_1 c_3 - r_3 c_1)$ of $V$ are collinear.

For positive $r_i$, read as the radii of circles centered at the $c_i$, these points are the
external homothety centers of the pairs of circles. If $r_i$ and $r_j$ have opposite signs, the
point $(r_i - r_j)^{-1}(r_i c_j - r_j c_i)$ is instead the internal homothety center of the
circles of radii $|r_i|$ and $|r_j|$ centered at $c_i$ and $c_j$; for example $r_1 = -1$ and
$r_2 = 2$ give $\frac{1}{3}(c_2 + 2 c_1)$. -/
theorem monge_three_circles_general {V : Type*} [AddCommGroup V] [Module ℝ V] {c₁ c₂ c₃ : V}
    {r₁ r₂ r₃ : ℝ} (h12 : r₁ ≠ r₂) (h23 : r₂ ≠ r₃) (h13 : r₁ ≠ r₃) :
    Collinear ℝ ({(r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
      (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂),
      (r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁)} : Set V) := by
  have d12 : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr h12
  have d23 : r₂ - r₃ ≠ 0 := sub_ne_zero.mpr h23
  have d13 : r₁ - r₃ ≠ 0 := sub_ne_zero.mpr h13
  rcases eq_or_ne r₂ 0 with hr₂' | hr₂'
  · have e : (r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁) = (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂) := by
      subst hr₂'
      match_scalars <;> field_simp <;> ring
    rw [e, Set.insert_eq_of_mem (Set.mem_insert _ _)]
    exact collinear_pair ℝ _ _
  · have hmem : (r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁) ∈
        affineSpan ℝ ({(r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
          (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂)} : Set V) := by
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
      refine ⟨r₁ * (r₂ - r₃) / (r₂ * (r₁ - r₃)), ?_⟩
      rw [AffineMap.lineMap_apply]
      simp only [vadd_eq_add, vsub_eq_sub]
      match_scalars <;> field_simp <;> ring
    have hcol : Collinear ℝ ({(r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁),
        (r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
        (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂)} : Set V) :=
      collinear_insert_of_mem_affineSpan_pair hmem
    have hset : ({(r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁),
        (r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
        (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂)} : Set V) =
        {(r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
        (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂),
        (r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁)} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset] at hcol

set_option linter.unusedVariables false in
/-- **Monge's three-circle theorem.** Let $c_1, c_2, c_3$ be points of the Euclidean plane
$\mathbb{R}^2$ and let $r_1, r_2, r_3$ be pairwise distinct positive real numbers such that the
closed disks of radius $r_i$ centered at $c_i$ are pairwise disjoint. Then the external homothety
centers $(r_1 - r_2)^{-1}(r_1 c_2 - r_2 c_1)$, $(r_2 - r_3)^{-1}(r_2 c_3 - r_3 c_2)$ and
$(r_1 - r_3)^{-1}(r_1 c_3 - r_3 c_1)$ of the three pairs of circles are collinear.

Source: https://en.wikipedia.org/wiki/Monge%27s_theorem (statement monge-s1).
The source's hypothesis is that no circle lies inside another; the pairwise disjointness of the
closed disks (`hd12`, `hd23`, `hd13`) is stronger.
Omitted source case: the source also treats two circles of equal radius, whose external
tangents are parallel and meet at a point at infinity. The distinct-radii hypotheses `h12`,
`h23`, `h13` exclude it, and the affine formula for the centers cannot express it.
It follows from `monge_three_circles_general`; the positivity hypotheses `hr₁`, `hr₂`, `hr₃`
and the disjointness hypotheses are unused and keep the `Wanted` statement's shape.
Proves `Wanted` entry `monge_three_circles`.
-/
theorem monge_three_circles {c₁ c₂ c₃ : EuclideanSpace ℝ (Fin 2)} {r₁ r₂ r₃ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (h12 : r₁ ≠ r₂) (h23 : r₂ ≠ r₃) (h13 : r₁ ≠ r₃)
    (hd12 : Disjoint (Metric.closedBall c₁ r₁) (Metric.closedBall c₂ r₂))
    (hd23 : Disjoint (Metric.closedBall c₂ r₂) (Metric.closedBall c₃ r₃))
    (hd13 : Disjoint (Metric.closedBall c₁ r₁) (Metric.closedBall c₃ r₃)) :
    Collinear ℝ ({(r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
      (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂),
      (r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁)} : Set (EuclideanSpace ℝ (Fin 2))) :=
  monge_three_circles_general h12 h23 h13

end MetaMathlibExt
