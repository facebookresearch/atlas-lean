/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pick's theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.PicksTheorem` — pick (manifest `manifests/problems/pick.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.PicksTheoremWanted` namespace. Mathematical
statements are unchanged. Source: G. Pick, *Geometrisches zur Zahlenlehre* (1899). Knill, *Some fundamental theorems in mathematics*, §154.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.PicksTheoremWanted
namespace Geometry.PicksTheorem

/-!
# Pick's theorem

`pick` (Pick 1899): a simple lattice polygon has area `I + B/2 − 1`, with `I`/`B`
the interior/boundary lattice-point counts. Trusted helpers (`toPlane`,
`latPoly`, `inside`, `area`, `Adjacent`, `IsSimple`, `boundaryPts`,
`interiorPts`) are non-holes. Mathlib has `Polygon` and its boundary but no
polygon interior, lattice-point counts, or Pick's theorem.
Category-(b) candidate from §154 of the Knill survey.
-/

open MeasureTheory

/-- **Lattice points in the plane.** The map $\mathbb{Z}^2 \to \mathbb{R}^2$ sending a lattice
point $(a, b)$ to the point $(a, b)$ of the real plane. -/
def toPlane (z : ℤ × ℤ) : ℝ × ℝ := ((z.1 : ℝ), (z.2 : ℝ))

/-- **Lattice polygon.** Given integer points $v_0, \dots, v_{n-1} \in \mathbb{Z}^2$, the lattice
polygon on $v$ is the polygon in $\mathbb{R}^2$ with $n$ vertices whose $i$-th vertex is $v_i$,
viewed as a point of $\mathbb{R}^2$. -/
def latPoly {n : ℕ} (v : Fin n → ℤ × ℤ) : Polygon (ℝ × ℝ) n :=
  ⟨fun i => toPlane (v i)⟩

/-- **Region enclosed by a planar set.** For a set $S \subseteq \mathbb{R}^2$, the region enclosed
by $S$ is the set of points $x \notin S$ whose connected component in the complement
$\mathbb{R}^2 \setminus S$ is bounded. For a simple closed curve $S$ this is the Jordan interior. -/
def inside (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {x | x ∉ S ∧ Bornology.IsBounded (connectedComponentIn Sᶜ x)}

/-- **Enclosed area.** The area enclosed by a set $S \subseteq \mathbb{R}^2$ is the Lebesgue
measure, as a real number, of the region enclosed by $S$ (the points $x \notin S$ whose connected
component in $\mathbb{R}^2 \setminus S$ is bounded); it is taken to be $0$ when that measure is
infinite. -/
noncomputable def area (S : Set (ℝ × ℝ)) : ℝ := (volume (inside S)).toReal

/-- **Cyclically adjacent indices.** Two indices $i, j \in \{0, \dots, n-1\}$ are adjacent when
$j \equiv i + 1 \pmod n$ or $i \equiv j + 1 \pmod n$. -/
def Adjacent {n : ℕ} (i j : Fin n) : Prop :=
  finRotate n i = j ∨ finRotate n j = i

/-- **Simple polygon.** A polygon in $\mathbb{R}^2$ with vertices $p_0, \dots, p_{n-1}$ (indices
taken mod $n$) and edges the segments $e_i = [p_i, p_{i+1}]$ is simple when consecutive vertices
are distinct ($p_i \ne p_{i+1}$ for all $i$), any two edges $e_i$ and $e_j$ with $i \ne j$,
$j \not\equiv i + 1$ and $i \not\equiv j + 1 \pmod n$ are disjoint, and every two consecutive
edges meet only in their common vertex: $e_i \cap e_{i+1} = \{p_{i+1}\}$ for all $i$. -/
def IsSimple {n : ℕ} (poly : Polygon (ℝ × ℝ) n) : Prop :=
  poly.HasNondegenerateEdges ∧
  (∀ i j : Fin n, i ≠ j → ¬ Adjacent i j →
      Disjoint (poly.edgeSet ℝ i) (poly.edgeSet ℝ j)) ∧
  (∀ i : Fin n, poly.edgeSet ℝ i ∩ poly.edgeSet ℝ (finRotate n i)
      = {poly (finRotate n i)})

/-- **Number of boundary lattice points.** For integer points
$v_0, \dots, v_{n-1} \in \mathbb{Z}^2$, the number of lattice points $z \in \mathbb{Z}^2$ that lie
on the boundary (the union of the edges) of the lattice polygon on $v$. -/
noncomputable def boundaryPts {n : ℕ} (v : Fin n → ℤ × ℤ) : ℕ :=
  Nat.card {z : ℤ × ℤ | toPlane z ∈ (latPoly v).boundary (R := ℝ)}

/-- **Number of interior lattice points.** For integer points
$v_0, \dots, v_{n-1} \in \mathbb{Z}^2$, the number of lattice points $z \in \mathbb{Z}^2$ that lie
in the region enclosed by the boundary of the lattice polygon on $v$, that is, the points off the
boundary whose connected component in its complement is bounded. -/
noncomputable def interiorPts {n : ℕ} (v : Fin n → ℤ × ℤ) : ℕ :=
  Nat.card {z : ℤ × ℤ | toPlane z ∈ inside ((latPoly v).boundary (R := ℝ))}

/- **Pick's theorem.** A simple lattice polygon with `n ≥ 3` vertices has area
`I + B/2 − 1`. -/
/-- **Pick's theorem.** Let $n \ge 3$ and let $v_0, \dots, v_{n-1} \in \mathbb{Z}^2$ be integer
points such that the lattice polygon $P$ in $\mathbb{R}^2$ with vertices $v_0, \dots, v_{n-1}$ is
simple. Then the area of the region enclosed by the boundary of $P$ equals $I + B/2 - 1$, where
$I$ is the number of lattice points in that region and $B$ is the number of lattice points on the
boundary of $P$.

Source: G. Pick, *Geometrisches zur Zahlenlehre* (1899). Knill, *Some fundamental theorems in mathematics*, §154. Via leanprover/lean-eval@38361be, problem `pick`. -/
public theorem_wanted pick {n : ℕ} (hn : 3 ≤ n) (v : Fin n → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    area ((latPoly v).boundary (R := ℝ))
      = (interiorPts v : ℝ) + (boundaryPts v : ℝ) / 2 - 1

end Geometry.PicksTheorem

end MathlibExt.Geometry.PicksTheoremWanted
