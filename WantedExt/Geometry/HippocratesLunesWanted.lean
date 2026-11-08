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

/-- The coordinate plane. -/
abbrev Plane := ℝ × ℝ

/-- Planar determinant (signed area form). -/
def det2 (u v : Plane) : ℝ := u.1 * v.2 - u.2 * v.1

/-- Midpoint of two points. -/
noncomputable def midpoint (p q : Plane) : Plane := ((p.1 + q.1) / 2, (p.2 + q.2) / 2)

/-- Displacement vector. -/
def vec (p q : Plane) : Plane := (q.1 - p.1, q.2 - p.2)

/-- Squared Euclidean distance (not the product sup metric). -/
def euclideanDistSq (p q : Plane) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Closed half-disk with diameter `p q` on the side selected by `side`. -/
def closedHalfDisk (p q : Plane) (side : ℝ → Prop) : Set Plane :=
  {x | euclideanDistSq x (midpoint p q) ≤ euclideanDistSq p q / 4 ∧
    side (det2 (vec p q) (vec p x))}

/-- The right-angle vertex. -/
def A : Plane := (0, 0)
/-- The leg endpoint on the x-axis. -/
def B (a : ℝ) : Plane := (a, 0)
/-- The leg endpoint on the y-axis. -/
def C (b : ℝ) : Plane := (0, b)

/-- Semicircle on the hypotenuse, on the side of the right-angle vertex. -/
def hypotenuseSemidisk (a b : ℝ) : Set Plane :=
  closedHalfDisk (B a) (C b) (fun t => 0 ≤ t)

/-- The Hippocrates lune on the horizontal leg. -/
def horizontalLune (a b : ℝ) : Set Plane :=
  closedHalfDisk A (B a) (fun t => t ≤ 0) \ hypotenuseSemidisk a b

/-- The Hippocrates lune on the vertical leg. -/
def verticalLune (a b : ℝ) : Set Plane :=
  closedHalfDisk A (C b) (fun t => 0 ≤ t) \ hypotenuseSemidisk a b

/-- The right triangle. -/
def rightTriangle (a b : ℝ) : Set Plane :=
  convexHull ℝ ({A, B a, C b} : Set Plane)

/- **Hippocrates' theorem on lunes.** For a right triangle, the two lunes'
areas sum to the triangle's area. -/
/-- Source: Hippocrates of Chios (c. 440 BC). Knill, §166. Via leanprover/lean-eval@38361be, problem `hippocrates_lunes`. -/
public theorem_wanted hippocrates_lunes (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (horizontalLune a b) + volume (verticalLune a b) =
      volume (rightTriangle a b)

end Geometry.HippocratesLunes

end MathlibExt.Geometry.HippocratesLunesWanted
