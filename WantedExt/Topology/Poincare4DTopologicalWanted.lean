/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 4D topological Poincaré conjecture (Freedman)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.Poincare4DTopological` — poincare_4d_topological (manifest `manifests/problems/poincare_4d_topological.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.Poincare4DTopologicalWanted` namespace. Mathematical
statements are unchanged. Source: M. H. Freedman, The topology of four-dimensional manifolds, J. Differential Geom. 17 (1982), 357-453. Specialization of `proof_wanted ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere` in Mathlib/Geometry/Manifold/PoincareConjecture.lean.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.Poincare4DTopologicalWanted
namespace Topology

/-!
# 4D topological Poincaré conjecture (Freedman)

A specialization of mathlib's generalized `proof_wanted
ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere` in
`Mathlib/Geometry/Manifold/PoincareConjecture.lean`, restricted to
dimension 4: every Hausdorff 4-manifold homotopy-equivalent to the standard
4-sphere `𝕊⁴` is homeomorphic to `𝕊⁴`.

This is Michael Freedman's 1982 theorem (Freedman, *The topology of
four-dimensional manifolds*, J. Differential Geom. 17), for which he was
awarded the Fields Medal in 1986. The proof uses Casson handles and the
"Bing topology" infinite-process construction; the corresponding **smooth**
4D Poincaré conjecture (every smooth homotopy 4-sphere is diffeomorphic
to `𝕊⁴`) remains famously **open** and is not included as an eval problem.

mathlib has homotopy equivalences (`≃ₕ`), homeomorphisms (`≃ₜ`),
`ChartedSpace`, and the unit sphere as a topological space — but no Casson
handles, no Freedman's theorem, and no 4D Poincaré conjecture.
-/

open Metric (sphere)
open ContinuousMap

/- **4D topological Poincaré conjecture** (Freedman, 1982). Every Hausdorff
4-manifold that is homotopy-equivalent to the standard 4-sphere `𝕊⁴` is
homeomorphic to `𝕊⁴`. -/
/-- **Topological Poincaré conjecture in dimension 4.** Let $M$ be a Hausdorff space with an
atlas of charts to $\mathbb{R}^4$ (a topological 4-manifold without boundary, not assumed
second countable). If $M$ is homotopy equivalent to the unit sphere
$S^4 = \{x \in \mathbb{R}^5 : \|x\| = 1\}$, then $M$ is homeomorphic to $S^4$.

Source: M. H. Freedman, The topology of four-dimensional manifolds, J. Differential Geom. 17 (1982), 357-453. Specialization of `proof_wanted ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere` in Mathlib/Geometry/Manifold/PoincareConjecture.lean. Via leanprover/lean-eval@38361be, problem `poincare_4d_topological`. -/
public theorem_wanted poincare_4d_topological
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (_h : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 5)) 1)

end Topology

end MathlibExt.Topology.Poincare4DTopologicalWanted
