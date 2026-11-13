/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Milnor's exotic 7-sphere

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.MilnorExoticSphereSeven` — milnor_exotic_sphere_seven (manifest `manifests/problems/milnor_exotic_sphere_seven.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.MilnorExoticSphereSevenWanted` namespace. Mathematical
statements are unchanged. Source: J. Milnor, On manifolds homeomorphic to the 7-sphere, Ann. of Math. 64 (1956), 399-405. Recorded as a `proof_wanted` in Mathlib/Geometry/Manifold/PoincareConjecture.lean at rev 5450b53e5ddc.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.MilnorExoticSphereSevenWanted
namespace Topology

/-!
# Milnor's exotic 7-sphere

A `proof_wanted` in `Mathlib/Geometry/Manifold/PoincareConjecture.lean`. The
existence of a smooth 7-manifold `M` that is homeomorphic to the standard
7-sphere `𝕊⁷` but **not** diffeomorphic to it.

This is John Milnor's 1956 discovery (Milnor, *On manifolds homeomorphic to
the 7-sphere*, Ann. of Math. 64) — the birth of differential topology as a
distinct subject from topology. Milnor exhibited his exotic 7-spheres as
`S³`-bundles over `S⁴` with non-standard smooth structure; their
non-diffeomorphism to `𝕊⁷` is detected by an invariant (Milnor's λ) built
from the signature of an 8-manifold bounding the candidate via Hirzebruch's
signature theorem and an integrality argument that distinguishes the
smooth structures.

mathlib has `ChartedSpace`, `IsManifold`, `Diffeomorph`, `Homeomorph`, and
the unit sphere as a smooth manifold (`Geometry/Manifold/Instances/Sphere.lean`),
but no exotic sphere construction. The statement here is the existential
form recorded as `proof_wanted exists_homeomorph_isEmpty_diffeomorph_sphere_seven`
in mathlib (the eval-problem flavour is the same — produce a smooth
structure on some `M ≃ₜ 𝕊⁷` for which no diffeomorphism `M ≃ₘ⟮𝓡 7, 𝓡 7⟯ 𝕊⁷`
exists).
-/

open scoped Manifold ContDiff
open Metric (sphere)

/- **Milnor's exotic 7-sphere.** There exists a smooth 7-manifold
homeomorphic to the standard 7-sphere `𝕊⁷` but not diffeomorphic to it. -/
/-- **Milnor's exotic 7-sphere.** There is a smooth manifold $M$ modelled on $\mathbb{R}^7$ (a
topological space with a $C^\infty$ atlas of charts into $\mathbb{R}^7$) that is homeomorphic to
the unit sphere $S^7 \subset \mathbb{R}^8$ but is not diffeomorphic to $S^7$ with its standard
smooth structure.

Source: J. Milnor, On manifolds homeomorphic to the 7-sphere, Ann. of Math. 64 (1956), 399-405. Recorded as a `proof_wanted` in Mathlib/Geometry/Manifold/PoincareConjecture.lean at rev 5450b53e5ddc. Via leanprover/lean-eval@38361be, problem `milnor_exotic_sphere_seven`. -/
public theorem_wanted milnor_exotic_sphere_seven :
    ∃ (M : Type) (_ : TopologicalSpace M)
      (_ : ChartedSpace (EuclideanSpace ℝ (Fin 7)) M)
      (_ : IsManifold (𝓡 7) ∞ M)
      (_homeo : M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 8)) 1),
      IsEmpty (M ≃ₘ⟮𝓡 7, 𝓡 7⟯ sphere (0 : EuclideanSpace ℝ (Fin 8)) 1)

end Topology

end MathlibExt.Topology.MilnorExoticSphereSevenWanted
