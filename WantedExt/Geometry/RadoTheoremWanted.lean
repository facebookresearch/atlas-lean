/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Radó's theorem on Riemann surfaces

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.RadoTheorem` — rado_riemannSurface (manifest `manifests/problems/rado_riemannSurface.toml`, rev 1, submitter Junyan Xu, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.RadoTheoremWanted` namespace. Mathematical
statements are unchanged. Source: John Hamal Hubbard, *Teichmüller theory and applications to geometry, topology, and dynamics. Vol. 1*, §1.3.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic

@[expose] public section

namespace MathlibExt.Geometry.RadoTheoremWanted
/-!
# Radó's theorem on Riemann surfaces

Every connected Riemann surface is second-countable (Tibor Radó, 1925).
A prerequisite to the uniformization theorem in John Hamal Hubbard,
*Teichmüller theory and applications to geometry, topology, and dynamics. Vol. 1* (§1.3).

See also https://en.wikipedia.org/wiki/Rad%C3%B3%27s_theorem_(Riemann_surfaces)
-/

namespace Geometry

/-- **Radó's theorem.** Every connected Riemann surface is second countable: if $X$ is a
connected Hausdorff topological space with an atlas of charts to $\mathbb{C}$ whose transition
maps are of class $C^1$ over $\mathbb{C}$ (that is, holomorphic), then the topology of $X$ is
second countable.

Source: John Hamal Hubbard, *Teichmüller theory and applications to geometry, topology, and dynamics. Vol. 1*, §1.3. Via leanprover/lean-eval@38361be, problem `rado_riemannSurface`. -/
public theorem_wanted rado_riemannSurface {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] :
    SecondCountableTopology X

end Geometry

end MathlibExt.Geometry.RadoTheoremWanted
