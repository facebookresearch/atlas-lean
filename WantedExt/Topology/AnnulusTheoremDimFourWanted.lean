/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Annulus Theorem in dimension 4 (Quinn)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.AnnulusTheoremDimFour` — annulus_theorem_dim_four (manifest `manifests/problems/annulus_theorem_dim_four.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.AnnulusTheoremDimFourWanted` namespace. The shared annulus infrastructure is imported from `WantedExt.Topology.AnnulusShared` instead of being copied here. Mathematical
statements are unchanged. Source: F. Quinn, *Ends of maps III: dimensions 4 and 5*, J. Differential Geom. 17 (1982), building on M. H. Freedman, *The topology of four-dimensional manifolds*, J. Differential Geom. 17 (1982).
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.AnnulusShared
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.AnnulusTheoremDimFourWanted
namespace Topology

open MathlibExt.Topology.AnnulusShared

open scoped unitInterval

/-!
# The Annulus Theorem in dimension 4 (Quinn, 1982)

The closed region between two disjoint, nested, locally flat embedded `3`-spheres
in `ℝ⁴` is homeomorphic to `S³ × [0,1]`. This four-dimensional case of the
annulus theorem is of an entirely different difficulty from the `n ≥ 5` case: it
was settled by Quinn (1982), building on Freedman's topology of 4-manifolds.

See `AnnulusShared` (`WantedExt.Topology.AnnulusShared`) for the shared definitions (`FlatSphere`, `inside`,
`regionBetween`, local flatness). The `n ≥ 5` case (Kirby) is a separate eval
problem, `annulus_theorem_high_dim`.
-/

/- **The Annulus Theorem in dimension `4`** (Quinn, 1982, building on Freedman).
Let `f` be a locally flat embedded `3`-sphere in `ℝ⁴` and `g` a second one nested
strictly inside `f`: the two images are disjoint and `g`'s image lies in the
inside of `f`. Then the closed region between them is homeomorphic to the product
`S³ × [0,1]`. -/
/-- Source: F. Quinn, *Ends of maps III: dimensions 4 and 5*, J. Differential Geom. 17 (1982), building on M. H. Freedman, *The topology of four-dimensional manifolds*, J. Differential Geom. 17 (1982). Via leanprover/lean-eval@38361be, problem `annulus_theorem_dim_four`. -/
public theorem_wanted annulus_theorem_dim_four
    (f g : FlatSphere 4)
    (hdisj : Disjoint (Set.range f.toFun) (Set.range g.toFun))
    (hnest : Set.range g.toFun ⊆ inside (Set.range f.toFun)) :
    Nonempty ((regionBetween f g) ≃ₜ (Sph 4 × I))

end Topology

end MathlibExt.Topology.AnnulusTheoremDimFourWanted
