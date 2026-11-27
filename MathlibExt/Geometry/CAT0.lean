/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Isometry

/-!
# CAT(0) four-point comparison condition

This file defines the Berg--Nikolaev four-point comparison condition. For geodesic metric spaces,
this condition characterizes CAT(0) spaces. The definition is stated for an arbitrary metric space
because Mathlib does not yet provide a generic geodesic-space API.
-/

@[expose] public section

universe u v

/-- **CAT(0) four-point condition.** A metric space $X$ satisfies the CAT(0) four-point
comparison condition if for all points $x, y, z, w \in X$ (not necessarily distinct),
$$d(x, z)^2 + d(y, w)^2 \le d(x, y)^2 + d(y, z)^2 + d(z, w)^2 + d(w, x)^2,$$
that is, the sum of the squares of the diagonals of every quadrilateral $xyzw$ is at most the
sum of the squares of its sides.

For geodesic metric spaces this is equivalent to the usual Euclidean comparison-triangle
definition of a CAT(0) space. -/
def IsCAT0FourPoint (X : Type u) [MetricSpace X] : Prop :=
  ∀ x y z w : X,
    dist x z ^ 2 + dist y w ^ 2 ≤
      dist x y ^ 2 + dist y z ^ 2 + dist z w ^ 2 + dist w x ^ 2

/-- **Unfolding the CAT(0) four-point condition.** A metric space $X$ satisfies the CAT(0)
four-point condition if and only if for all points $x, y, z, w \in X$,
$$d(x, z)^2 + d(y, w)^2 \le d(x, y)^2 + d(y, z)^2 + d(z, w)^2 + d(w, x)^2.$$
-/
theorem isCAT0FourPoint_iff {X : Type u} [MetricSpace X] :
    IsCAT0FourPoint X ↔
      ∀ x y z w : X,
        dist x z ^ 2 + dist y w ^ 2 ≤
          dist x y ^ 2 + dist y z ^ 2 + dist z w ^ 2 + dist w x ^ 2 :=
  Iff.rfl

namespace IsCAT0FourPoint

/-- **The CAT(0) four-point condition passes to isometrically embedded spaces.** Let $X$ and $Y$
be metric spaces and let $f : X \to Y$ be an isometry, that is, $d(f(a), f(b)) = d(a, b)$ for
all $a, b \in X$. If $Y$ satisfies the CAT(0) four-point condition, then so does $X$. -/
theorem of_isometry {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (hY : IsCAT0FourPoint Y) {f : X → Y} (hf : Isometry f) : IsCAT0FourPoint X := by
  intro x y z w
  simpa only [hf.dist_eq] using hY (f x) (f y) (f z) (f w)

/-- **Isometry invariance of the CAT(0) four-point condition.** If $X$ and $Y$ are metric spaces
and there is an isometric bijection from $X$ onto $Y$, then $X$ satisfies the CAT(0) four-point
condition if and only if $Y$ does. -/
theorem iff_of_isometryEquiv {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ Y) : IsCAT0FourPoint X ↔ IsCAT0FourPoint Y :=
  ⟨fun hX ↦ of_isometry hX e.symm.isometry, fun hY ↦ of_isometry hY e.isometry⟩

/-- **Spaces with at most one point satisfy the CAT(0) four-point condition.** Every metric
space with at most one point (including the empty space) satisfies the CAT(0) four-point
condition. -/
theorem of_subsingleton (X : Type u) [MetricSpace X] [Subsingleton X] : IsCAT0FourPoint X := by
  intro x y z w
  have hxy : x = y := Subsingleton.elim _ _
  have hxz : x = z := Subsingleton.elim _ _
  have hxw : x = w := Subsingleton.elim _ _
  subst y
  subst z
  subst w
  simp

end IsCAT0FourPoint

-- An inhabited singleton is a basic example.
example : IsCAT0FourPoint PUnit := IsCAT0FourPoint.of_subsingleton PUnit

-- The empty metric space is the boundary case; the comparison is vacuous.
example : IsCAT0FourPoint Empty := IsCAT0FourPoint.of_subsingleton Empty
