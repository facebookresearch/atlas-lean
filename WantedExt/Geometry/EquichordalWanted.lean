/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equichordal point theorem (convex curves have a unique equichordal point)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.Equichordal` — equichordal_point_unique (manifest `manifests/problems/equichordal_point_unique.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.EquichordalWanted` namespace. Mathematical
statements are unchanged. Source: M. R. Rychlik, A complete solution to the equichordal point problem of Fujiwara, Blaschke, Rothe and Weizenböck, Invent. Math. 129 (1997). Listed as §205 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §205.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.EquichordalWanted
namespace Geometry.Equichordal

/-!
# Equichordal point theorem

`equichordal_point_unique`: a smooth convex plane curve, packaged as the
frontier of a compact convex planar domain `K` with nonempty interior, cannot
have two distinct equichordal points. The helper `IsEquichordalPoint` records
that the sum of the two opposite radial chord distances through an interior
point is a direction-independent constant. Mathlib has no equichordal-point
result. Category-(b) candidate from §205 of the Knill survey.
-/

open Metric Set

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A point `P` is equichordal for the boundary of a planar domain `K` if
there is a constant chord length `L` such that every unit direction through
`P` meets the boundary at opposite chord endpoints whose total chord length
is `L`.  The open segment condition rules out choosing non-endpoint boundary
crossings for nonconvex star-like domains. -/
def IsEquichordalPoint (K : Set Plane) (P : Plane) : Prop :=
  P ∈ interior K ∧
    ∃ L : ℝ, 0 < L ∧
      ∀ u : Plane, u ∈ sphere (0 : Plane) 1 →
        ∃ a b : ℝ,
          0 < a ∧ 0 < b ∧
            P + a • u ∈ frontier K ∧
              P - b • u ∈ frontier K ∧
                openSegment ℝ (P - b • u) (P + a • u) ⊆ interior K ∧
                  dist (P + a • u) (P - b • u) = L

/- **Equichordal point theorem** (§205).  A convex planar curve cannot have
two distinct equichordal points. -/
/-- Source: M. R. Rychlik, A complete solution to the equichordal point problem of Fujiwara, Blaschke, Rothe and Weizenböck, Invent. Math. 129 (1997). Listed as §205 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §205. Via leanprover/lean-eval@38361be, problem `equichordal_point_unique`. -/
public theorem_wanted equichordal_point_unique {K : Set Plane}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty) :
    ¬ ∃ P Q : Plane,
      P ≠ Q ∧ IsEquichordalPoint K P ∧ IsEquichordalPoint K Q

end Geometry.Equichordal

end MathlibExt.Geometry.EquichordalWanted
