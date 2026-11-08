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

/-- Coordinatewise cast of a lattice point to the plane. -/
def toPlane (z : ℤ × ℤ) : ℝ × ℝ := ((z.1 : ℝ), (z.2 : ℝ))

/-- The lattice polygon on integer vertex data `v`. -/
def latPoly {n : ℕ} (v : Fin n → ℤ × ℤ) : Polygon (ℝ × ℝ) n :=
  ⟨fun i => toPlane (v i)⟩

/-- The open interior region of a planar curve `S`: points off `S` whose
component in `Sᶜ` is bounded (the Jordan interior for a simple closed curve). -/
def inside (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {x | x ∉ S ∧ Bornology.IsBounded (connectedComponentIn Sᶜ x)}

/-- Enclosed area: Lebesgue measure of the interior region. -/
noncomputable def area (S : Set (ℝ × ℝ)) : ℝ := (volume (inside S)).toReal

/-- Cyclic adjacency of edge indices. -/
def Adjacent {n : ℕ} (i j : Fin n) : Prop :=
  finRotate n i = j ∨ finRotate n j = i

/-- A simple (Jordan) polygon. -/
def IsSimple {n : ℕ} (poly : Polygon (ℝ × ℝ) n) : Prop :=
  poly.HasNondegenerateEdges ∧
  (∀ i j : Fin n, i ≠ j → ¬ Adjacent i j →
      Disjoint (poly.edgeSet ℝ i) (poly.edgeSet ℝ j)) ∧
  (∀ i : Fin n, poly.edgeSet ℝ i ∩ poly.edgeSet ℝ (finRotate n i)
      = {poly (finRotate n i)})

/-- Number of boundary lattice points. -/
noncomputable def boundaryPts {n : ℕ} (v : Fin n → ℤ × ℤ) : ℕ :=
  Nat.card {z : ℤ × ℤ | toPlane z ∈ (latPoly v).boundary (R := ℝ)}

/-- Number of interior lattice points. -/
noncomputable def interiorPts {n : ℕ} (v : Fin n → ℤ × ℤ) : ℕ :=
  Nat.card {z : ℤ × ℤ | toPlane z ∈ inside ((latPoly v).boundary (R := ℝ))}

/- **Pick's theorem.** A simple lattice polygon with `n ≥ 3` vertices has area
`I + B/2 − 1`. -/
/-- Source: G. Pick, *Geometrisches zur Zahlenlehre* (1899). Knill, *Some fundamental theorems in mathematics*, §154. Via leanprover/lean-eval@38361be, problem `pick`. -/
public theorem_wanted pick {n : ℕ} (hn : 3 ≤ n) (v : Fin n → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    area ((latPoly v).boundary (R := ℝ))
      = (interiorPts v : ℝ) + (boundaryPts v : ℝ) / 2 - 1

end Geometry.PicksTheorem

end MathlibExt.Geometry.PicksTheoremWanted
