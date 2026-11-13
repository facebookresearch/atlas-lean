/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3D topological Poincaré conjecture (Perelman)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.Poincare3DTopological` — poincare_3d_topological (manifest `manifests/problems/poincare_3d_topological.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.Poincare3DTopologicalWanted` namespace. Mathematical
statements are unchanged, with the correction that `[Nonempty M]` is added (the empty type otherwise satisfies the hypotheses vacuously). Source: G. Perelman, The entropy formula for the Ricci flow and its geometric applications (arXiv:math/0211159, 2002); Ricci flow with surgery on three-manifolds (arXiv:math/0303109, 2003); Finite extinction time for the solutions to the Ricci flow on certain three-manifolds (arXiv:math/0307245, 2003). Recorded as a `proof_wanted` in Mathlib/Geometry/Manifold/PoincareConjecture.lean. Originally conjectured by Henri Poincaré in 1904.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.Poincare3DTopologicalWanted
namespace Topology

/-!
# 3D topological Poincaré conjecture (Perelman)

A `proof_wanted` in `Mathlib/Geometry/Manifold/PoincareConjecture.lean`. Every
simply connected compact Hausdorff 3-manifold is homeomorphic to the standard
3-sphere `𝕊³`.

Proved by Grigori Perelman in 2002–2003 via Hamilton's Ricci flow with surgery
(Perelman's three preprints on the arXiv; Fields Medal awarded but declined,
2006; Clay Millennium Prize awarded 2010, also declined). One of the seven
original Millennium Problems.

mathlib has `ChartedSpace`, `SimplyConnectedSpace`, `CompactSpace`, `T2Space`,
`Homeomorph` (`≃ₜ`), and the unit sphere as a smooth manifold but no
Ricci flow, no Hamilton–Perelman surgery, and no Poincaré conjecture itself.
-/

open Metric (sphere)

/- **3D topological Poincaré conjecture** (Perelman, 2002–2003). Every
simply connected compact Hausdorff 3-manifold is homeomorphic to the
standard 3-sphere `𝕊³`. -/
/-- **Topological Poincaré conjecture in dimension 3.** Let $M$ be a nonempty, compact, simply
connected Hausdorff space with an atlas of charts to $\mathbb{R}^3$, that is, a topological
3-manifold without boundary. Then $M$ is homeomorphic to the unit sphere
$S^3 = \{x \in \mathbb{R}^4 : \|x\| = 1\}$.

Source: G. Perelman, The entropy formula for the Ricci flow and its geometric applications (arXiv:math/0211159, 2002); Ricci flow with surgery on three-manifolds (arXiv:math/0303109, 2003); Finite extinction time for the solutions to the Ricci flow on certain three-manifolds (arXiv:math/0307245, 2003). Recorded as a `proof_wanted` in Mathlib/Geometry/Manifold/PoincareConjecture.lean. Originally conjectured by Henri Poincaré in 1904. Via leanprover/lean-eval@38361be, problem `poincare_3d_topological`. -/
public theorem_wanted poincare_3d_topological
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] [Nonempty M] :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

end Topology

end MathlibExt.Topology.Poincare3DTopologicalWanted
