/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dehn–Sommerville equations for simplicial spheres

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.DehnSommerville` — dehn_sommerville (manifest `manifests/problems/dehn_sommerville.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.DehnSommervilleWanted` namespace. Mathematical
statements are unchanged. Source: M. Dehn (1905); D. M. Y. Sommerville (1927); see Stanley, *Combinatorics and Commutative Algebra*. Knill, *Some fundamental theorems in mathematics*, §142.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Combinatorics.SimplicialSphereShared
public import Mathlib

@[expose] public section

open MathlibExt.Combinatorics.SimplicialSphereShared

namespace MathlibExt.Combinatorics.DehnSommervilleWanted
namespace Combinatorics.DehnSommerville

/-!
# The Dehn–Sommerville equations for simplicial spheres

`dehn_sommerville`: the h-vector of a finite simplicial `(d-1)`-sphere is
symmetric, `h_j = h_{d-j}`. Trusted helpers (`FiniteSimplicialSphere`,
`faceCount`, `extendedFaceCount`, `hVector`) are non-holes. Mathlib has
simplicial complexes but no f- or h-vector or Dehn–Sommerville theory. (The
companion upper-bound theorem for simplicial spheres is already in lean-eval.)
Category-(b) candidate from §142 of the Knill survey.
-/





/- **Dehn–Sommerville equations.** The h-vector of a finite simplicial sphere
is symmetric: `h_j = h_{d-j}`. -/
/-- Source: M. Dehn (1905); D. M. Y. Sommerville (1927); see Stanley, *Combinatorics and Commutative Algebra*. Knill, *Some fundamental theorems in mathematics*, §142. Via leanprover/lean-eval@38361be, problem `dehn_sommerville`. -/
public theorem_wanted dehn_sommerville
    {d j : ℕ} (X : FiniteSimplicialSphere d) (hj : j ≤ d) :
    hVector X j = hVector X (d - j)

end Combinatorics.DehnSommerville

end MathlibExt.Combinatorics.DehnSommervilleWanted
