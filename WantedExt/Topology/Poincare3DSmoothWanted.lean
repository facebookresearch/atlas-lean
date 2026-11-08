/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3D smooth Poincaré conjecture (Perelman)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.Poincare3DSmooth` — poincare_3d_smooth (manifest `manifests/problems/poincare_3d_smooth.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.Poincare3DSmoothWanted` namespace. Mathematical
statements are unchanged, with the correction that `[Nonempty M]` is added (the empty type otherwise satisfies the hypotheses vacuously). Source: G. Perelman, three arXiv preprints 2002-2003 (math/0211159, math/0303109, math/0307245). Recorded as a `proof_wanted` in Mathlib/Geometry/Manifold/PoincareConjecture.lean. In dim 3, Smooth ⇔ PL ⇔ Topological via Moise (1952) / Bing (1959).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.Poincare3DSmoothWanted
namespace Topology

/-!
# 3D smooth Poincaré conjecture (Perelman)

A `proof_wanted` in `Mathlib/Geometry/Manifold/PoincareConjecture.lean`. Every
simply connected compact Hausdorff 3-manifold that admits a smooth structure
is **diffeomorphic** to the standard 3-sphere `𝕊³`.

This is the smooth-category strengthening of the topological 3D Poincaré
conjecture, also proved by Perelman in 2002–2003. In dimension 3 the smooth
and topological Poincaré conjectures are equivalent (every topological
3-manifold admits a unique smooth structure, by Moise's theorem), but the
formal Lean statement carries the smooth structure explicitly via
`IsManifold (𝓡 3) ∞ M` and concludes with a diffeomorphism in the manifold
type `M ≃ₘ⟮𝓡 3, 𝓡 3⟯ 𝕊³`.

mathlib has `ChartedSpace`, `IsManifold`, `Diffeomorph`, `SimplyConnectedSpace`,
`CompactSpace`, and the unit sphere as a smooth manifold but no Ricci flow,
no Hamilton–Perelman surgery, and no Moise theorem.
-/

open scoped Manifold ContDiff
open Metric (sphere)

/- **3D smooth Poincaré conjecture** (Perelman, 2002–2003). Every simply
connected compact Hausdorff smooth 3-manifold is diffeomorphic to the
standard 3-sphere `𝕊³`. -/
/-- Source: G. Perelman, three arXiv preprints 2002-2003 (math/0211159, math/0303109, math/0307245). Recorded as a `proof_wanted` in Mathlib/Geometry/Manifold/PoincareConjecture.lean. In dim 3, Smooth ⇔ PL ⇔ Topological via Moise (1952) / Bing (1959). Via leanprover/lean-eval@38361be, problem `poincare_3d_smooth`. -/
public theorem_wanted poincare_3d_smooth
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [SimplyConnectedSpace M] [CompactSpace M] [Nonempty M] :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

end Topology

end MathlibExt.Topology.Poincare3DSmoothWanted
