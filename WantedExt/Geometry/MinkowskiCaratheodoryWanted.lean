/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minkowski-Caratheodory theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ConvexGeometry.MinkowskiCaratheodory` — mem_convexHull_finset_extremePoints_of_mem_compact_convex (manifest `manifests/problems/mem_convexHull_finset_extremePoints_of_mem_compact_convex.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.MinkowskiCaratheodoryWanted` namespace. Mathematical
statements are unchanged. Source: Classical theorem in convex geometry.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.KreinMilman

@[expose] public section

namespace MathlibExt.Geometry.MinkowskiCaratheodoryWanted
namespace ConvexGeometry

open Set

/-!
Minkowski-Carathéodory theorem in finite-dimensional real normed spaces.

This formulation packages the theorem as a finite extreme-point representation for each point of a
compact convex set, with the expected `finrank + 1` bound on the number of points used.
-/

public theorem_wanted mem_convexHull_finset_extremePoints_of_mem_compact_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E}
    (hscomp : IsCompact s)
    (hsconv : Convex ℝ s)
    (hx : x ∈ s) :
    ∃ t : Finset E,
      (↑t : Set E) ⊆ s.extremePoints ℝ ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E)

end ConvexGeometry

end MathlibExt.Geometry.MinkowskiCaratheodoryWanted
