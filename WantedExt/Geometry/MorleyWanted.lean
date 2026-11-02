/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Morley's trisector theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.Morley` — morley_theorem (manifest `manifests/problems/morley_theorem.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.MorleyWanted` namespace. Mathematical
statements are unchanged. Source: F. Morley (c. 1899). Knill, §162.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.MorleyWanted
namespace Geometry.Morley

/-!
# Morley's trisector theorem

`morley_theorem`: the triangle formed by the adjacent angle-trisectors of any
nondegenerate Euclidean triangle is equilateral. Trusted helpers
(`IsEquilateralTriple`, `LiesInTriangle`, `IsMorleyConfiguration`) are
non-holes. Mathlib has Euclidean angles but not Morley's theorem.
Category-(b) candidate from §162 of the Knill survey.
-/

open scoped EuclideanGeometry

/-- **Euclidean plane for Morley's theorem.** The Euclidean plane $\mathbb{R}^2$ with its
standard Euclidean distance. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **Equilateral triple of points.** Three points $P$, $Q$, $R$ of the Euclidean plane form an
equilateral triple when, writing $d$ for the Euclidean distance, $d(P, Q) = d(Q, R)$ and
$d(Q, R) = d(R, P)$. Coincident points are allowed, so $P = Q = R$ qualifies. -/
def IsEquilateralTriple (P Q R : Plane) : Prop :=
  dist P Q = dist Q R ∧ dist Q R = dist R P

/-- **Point in a closed triangle.** A point $X$ of the Euclidean plane lies in the triangle with
vertices $A$, $B$, $C$ when $X$ belongs to the convex hull of $\{A, B, C\}$, the closed triangle
$ABC$ (a segment or a point when $A$, $B$, $C$ are collinear). -/
def LiesInTriangle (A B C X : Plane) : Prop :=
  X ∈ convexHull ℝ ({A, B, C} : Set Plane)

/-- **Morley configuration.** Points $A$, $B$, $C$, $P$, $Q$, $R$ of the Euclidean plane form a
Morley configuration when $A$, $B$, $C$ are not collinear, each of $P$, $Q$, $R$ lies in the
closed triangle $ABC$, and, writing $\angle XYZ \in [0, \pi]$ for the unoriented angle at $Y$,
$0 < \angle CAR = \angle RAP = \angle PAB$ and $3 \angle PAB = \angle CAB$;
$0 < \angle ABP = \angle PBQ = \angle QBC$ and $3 \angle QBC = \angle ABC$;
$0 < \angle BCQ = \angle QCR = \angle RCA$ and $3 \angle RCA = \angle BCA$.
Thus $P$, $Q$, $R$ are the intersections of adjacent angle trisectors of the triangle $ABC$. -/
def IsMorleyConfiguration (A B C P Q R : Plane) : Prop :=
  ¬ Collinear ℝ ({A, B, C} : Set Plane) ∧
  LiesInTriangle A B C P ∧ LiesInTriangle A B C Q ∧ LiesInTriangle A B C R ∧
  0 < (∠ C A R) ∧ (∠ C A R) = (∠ R A P) ∧ (∠ R A P) = (∠ P A B) ∧
  3 * (∠ P A B) = (∠ C A B) ∧
  0 < (∠ A B P) ∧ (∠ A B P) = (∠ P B Q) ∧ (∠ P B Q) = (∠ Q B C) ∧
  3 * (∠ Q B C) = (∠ A B C) ∧
  0 < (∠ B C Q) ∧ (∠ B C Q) = (∠ Q C R) ∧ (∠ Q C R) = (∠ R C A) ∧
  3 * (∠ R C A) = (∠ B C A)

/- **Morley's theorem.** The adjacent-trisector triangle `PQR` of a
nondegenerate triangle `ABC` is equilateral. -/
/-- **Morley's trisector theorem.** If points $A$, $B$, $C$, $P$, $Q$, $R$ of the Euclidean plane
form a Morley configuration, so that $ABC$ is a nondegenerate triangle and $P$, $Q$, $R$ are the
intersections of its adjacent angle trisectors, then $P$, $Q$, $R$ form an equilateral triple:
writing $d$ for the Euclidean distance, $d(P, Q) = d(Q, R)$ and $d(Q, R) = d(R, P)$.

Source: F. Morley (c. 1899). Knill, §162. Via leanprover/lean-eval@38361be, problem `morley_theorem`. -/
public theorem_wanted morley_theorem (A B C P Q R : Plane)
    (h : IsMorleyConfiguration A B C P Q R) :
    IsEquilateralTriple P Q R

end Geometry.Morley

end MathlibExt.Geometry.MorleyWanted
