/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hippocrates' theorem on lunes

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.HippocratesLunes` — hippocrates_lunes (manifest `manifests/problems/hippocrates_lunes.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.HippocratesLunesWanted` namespace. Mathematical
statements are unchanged. Source: Hippocrates of Chios (c. 440 BC). Knill, §166.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.HippocratesLunesWanted
namespace Geometry.HippocratesLunes

/-!
# Hippocrates' theorem on lunes

`hippocrates_lunes`: for a right triangle, the sum of the areas of the two
Hippocrates lunes equals the area of the triangle. Trusted helpers (`det2`,
`closedHalfDisk`, `hypotenuseSemidisk`, `horizontalLune`, `verticalLune`,
`rightTriangle`, …) are non-holes; the Euclidean squared distance is used
explicitly to avoid the `ℝ × ℝ` sup metric turning disks into squares. Mathlib
has no lune/classical-area result of this kind.
Category-(b) candidate from §166 of the Knill survey.
-/

open MeasureTheory

/-- **Coordinate plane for Hippocrates' lunes.** The coordinate plane is the set
$\mathbb{R} \times \mathbb{R}$ of ordered pairs $(x, y)$ of real numbers. -/
abbrev Plane := ℝ × ℝ

/-- **Planar determinant for Hippocrates' lunes.** For vectors $u = (u_1, u_2)$ and
$v = (v_1, v_2)$ of the coordinate plane, $\det(u, v) = u_1 v_2 - u_2 v_1$, the signed area of
the parallelogram spanned by $u$ and $v$. -/
def det2 (u v : Plane) : ℝ := u.1 * v.2 - u.2 * v.1

/-- **Midpoint of two points in the plane.** For points $p = (p_1, p_2)$ and
$q = (q_1, q_2)$ of the coordinate plane, their midpoint is
$\left(\frac{p_1 + q_1}{2}, \frac{p_2 + q_2}{2}\right)$. -/
noncomputable def midpoint (p q : Plane) : Plane := ((p.1 + q.1) / 2, (p.2 + q.2) / 2)

/-- **Displacement vector between two points of the plane.** For points $p = (p_1, p_2)$ and
$q = (q_1, q_2)$ of $\mathbb{R}^2$, the displacement vector from $p$ to $q$ is
$(q_1 - p_1, q_2 - p_2)$. -/
def vec (p q : Plane) : Plane := (q.1 - p.1, q.2 - p.2)

/-- **Squared Euclidean distance in the plane.** For points $p = (p_1, p_2)$ and
$q = (q_1, q_2)$ of the coordinate plane, the squared Euclidean distance between them is
$(p_1 - q_1)^2 + (p_2 - q_2)^2$.

This uses the Euclidean distance, not the sup metric of the product
$\mathbb{R} \times \mathbb{R}$. -/
def euclideanDistSq (p q : Plane) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- **Closed half-disk on a diameter.** Given points $p$ and $q$ of the coordinate plane and a
property $S$ of real numbers, this is the set of points $x$ such that the squared Euclidean
distance from $x$ to the midpoint of $p$ and $q$ is at most one quarter of the squared Euclidean
distance from $p$ to $q$ (so $x$ lies in the closed disk with diameter $pq$), and $S$ holds of
the planar determinant $\det(q - p, x - p)$. For $p \ne q$, taking $S(t)$ to be $t \ge 0$
(respectively $t \le 0$) selects the closed half of that disk to the left (respectively right)
of the directed line from $p$ to $q$. -/
def closedHalfDisk (p q : Plane) (side : ℝ → Prop) : Set Plane :=
  {x | euclideanDistSq x (midpoint p q) ≤ euclideanDistSq p q / 4 ∧
    side (det2 (vec p q) (vec p x))}

/-- **Right-angle vertex of the lune triangle.** The point $A = (0, 0)$, the origin of the
coordinate plane; it is the right-angle vertex of the triangle in Hippocrates' theorem on
lunes. -/
def A : Plane := (0, 0)
/-- **Horizontal leg endpoint of the lune triangle.** For a real number $a$, the point
$B = (a, 0)$ on the $x$-axis of the coordinate plane; it is the endpoint of the horizontal leg of
the right triangle in Hippocrates' theorem on lunes. -/
def B (a : ℝ) : Plane := (a, 0)
/-- **Vertical leg endpoint of the lune triangle.** For a real number $b$, the point
$C = (0, b)$ on the $y$-axis of the coordinate plane; it is the endpoint of the vertical leg of
the right triangle in Hippocrates' theorem on lunes. -/
def C (b : ℝ) : Plane := (0, b)

/-- **Half-disk on the hypotenuse.** For real numbers $a$ and $b$, let $B = (a, 0)$ and
$C = (0, b)$. The half-disk on the hypotenuse is the set of points $x = (x_1, x_2)$ of the
closed disk with diameter $BC$ satisfying $\det(C - B, x - B) \ge 0$, that is,
$b x_1 + a x_2 \le ab$. For $a, b > 0$ this is the half of the disk on the side of the line
$BC$ containing the right-angle vertex $(0, 0)$. -/
def hypotenuseSemidisk (a b : ℝ) : Set Plane :=
  closedHalfDisk (B a) (C b) (fun t => 0 ≤ t)

/-- **Lune on the horizontal leg.** For real numbers $a$ and $b$, let $A = (0, 0)$,
$B = (a, 0)$ and $C = (0, b)$. The lune on the horizontal leg is the set of points
$x = (x_1, x_2)$ of the closed disk with diameter $AB$ satisfying $a x_2 \le 0$ that do not
lie in the half-disk on the hypotenuse, the set of points of the closed disk with diameter $BC$
satisfying $b x_1 + a x_2 \le ab$. For $a, b > 0$ this is the set of points of the closed lower
half-disk on the leg $AB$ that lie outside the closed disk with diameter $BC$. -/
def horizontalLune (a b : ℝ) : Set Plane :=
  closedHalfDisk A (B a) (fun t => t ≤ 0) \ hypotenuseSemidisk a b

/-- **Hippocrates lune on the vertical leg.** For real numbers $a$ and $b$, the vertical lune is
the set of points $(x, y) \in \mathbb{R}^2$ with $x^2 + (y - b/2)^2 \le b^2/4$ and $bx \le 0$
that do not satisfy both $(x - a/2)^2 + (y - b/2)^2 \le (a^2 + b^2)/4$ and $bx + ay \le ab$.

For $a, b > 0$ this is the closed half-disk on the segment from $(0, 0)$ to $(0, b)$, on the side
away from $(a, 0)$, minus the closed half-disk on the hypotenuse from $(a, 0)$ to $(0, b)$, on
the side of the origin. -/
def verticalLune (a b : ℝ) : Set Plane :=
  closedHalfDisk A (C b) (fun t => 0 ≤ t) \ hypotenuseSemidisk a b

/-- **Right triangle with legs on the axes.** For real numbers $a$ and $b$, the right triangle
$T(a, b)$ is the convex hull in the plane $\mathbb{R}^2$ of the three points $(0, 0)$, $(a, 0)$
and $(0, b)$. -/
def rightTriangle (a b : ℝ) : Set Plane :=
  convexHull ℝ ({A, B a, C b} : Set Plane)

/- **Hippocrates' theorem on lunes.** For a right triangle, the two lunes'
areas sum to the triangle's area. -/
/-- **Hippocrates' theorem on lunes.** Let $a, b > 0$ and consider the right triangle with
vertices $A = (0, 0)$, $B = (a, 0)$ and $C = (0, b)$. The Lebesgue measure of the lune on the
horizontal leg plus the Lebesgue measure of the lune on the vertical leg equals the Lebesgue
measure of the triangle, that is, of the convex hull of $A$, $B$ and $C$.

Source: Hippocrates of Chios (c. 440 BC). Knill, §166. Via leanprover/lean-eval@38361be, problem `hippocrates_lunes`. -/
public theorem_wanted hippocrates_lunes (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (horizontalLune a b) + volume (verticalLune a b) =
      volume (rightTriangle a b)

end Geometry.HippocratesLunes

end MathlibExt.Geometry.HippocratesLunesWanted
