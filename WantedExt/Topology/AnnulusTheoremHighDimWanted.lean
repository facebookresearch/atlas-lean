/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Annulus Theorem in dimension ≥ 5 (Kirby)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.AnnulusTheoremHighDim` — annulus_theorem_high_dim (manifest `manifests/problems/annulus_theorem_high_dim.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.AnnulusTheoremHighDimWanted` namespace. The shared annulus infrastructure is imported from `WantedExt.Topology.AnnulusShared` instead of being copied here. Mathematical
statements are unchanged. Source: R. C. Kirby, *Stable homeomorphisms and the annulus conjecture*, Ann. of Math. 89 (1969).
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.AnnulusShared
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.AnnulusTheoremHighDimWanted
namespace Topology

open MathlibExt.Topology.AnnulusShared

open scoped unitInterval

/-!
# The Annulus Theorem in dimension ≥ 5 (Kirby, 1969)

The closed region between two disjoint, nested, locally flat embedded
`(n-1)`-spheres in `ℝⁿ`, for ambient dimension `n ≥ 5`, is homeomorphic to
`Sⁿ⁻¹ × [0,1]`. This was the hard core of Kirby's proof of the stable
homeomorphism conjecture, via the torus trick.

See `AnnulusShared` (`WantedExt.Topology.AnnulusShared`) for the shared definitions (`FlatSphere`, `inside`,
`regionBetween`, local flatness). The `n = 4` case (Quinn) is a separate eval
problem, `annulus_theorem_dim_four`, of a quite different difficulty.
-/

/- **The Annulus Theorem in dimension `≥ 5`** (Kirby, 1969). Let `f` be a
locally flat embedded `(n-1)`-sphere in `ℝⁿ` (`n ≥ 5`) and `g` a second one
nested strictly inside `f`: the two images are disjoint and `g`'s image lies in
the inside of `f`. Then the closed region between them is homeomorphic to the
product `Sⁿ⁻¹ × [0,1]`. -/
/-- Source: R. C. Kirby, *Stable homeomorphisms and the annulus conjecture*, Ann. of Math. 89 (1969). Via leanprover/lean-eval@38361be, problem `annulus_theorem_high_dim`. -/
public theorem_wanted annulus_theorem_high_dim {n : ℕ} [NeZero n] (hn : 5 ≤ n)
    (f g : FlatSphere n)
    (hdisj : Disjoint (Set.range f.toFun) (Set.range g.toFun))
    (hnest : Set.range g.toFun ⊆ inside (Set.range f.toFun)) :
    Nonempty ((regionBetween f g) ≃ₜ (Sph n × I))

end Topology

end MathlibExt.Topology.AnnulusTheoremHighDimWanted
