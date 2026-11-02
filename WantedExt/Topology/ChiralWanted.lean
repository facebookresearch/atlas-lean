/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Existence of a chiral oriented knot

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.KnotTheory.Chiral` — exists_chiral_knot (manifest `manifests/problems/exists_chiral_knot.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.ChiralWanted` namespace. The shared knot-theory prelude is imported from `WantedExt.Topology.ConwayKnotShared` instead of being copied here. Mathematical
statements are unchanged. Source: Classical; see https://en.wikipedia.org/wiki/Chirality_(mathematics) and https://en.wikipedia.org/wiki/Trefoil_knot.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.ConwayKnotShared
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace MathlibExt.Topology.ChiralWanted
namespace KnotTheory

open MathlibExt.Topology.ConwayKnotShared.KnotTheory

/-! The knot-theory model (`R3`, `Knot`, `TwoLink`, `AmbientIsotopy`,
`CircleReparam`, isotopy, `reflectZ`, chirality) is shared with the other
knot entries via `WantedExt.Topology.ConwayKnotShared` and is not copied
here, so all knot entries speak about the same `Knot` type. -/

/-!
# Existence of a chiral knot

The challenge problem of the knot-theory benchmark. Unlike the previous two
problems — where the relevant invariant is suggested explicitly — proving
chirality requires an invariant *that is not preserved under reflection*,
and choosing the right such invariant is part of the problem.
-/

/- **Existence of a chiral oriented smooth knot.**

There exists an oriented smooth knot in `ℝ³` that is not ambient-isotopic
to its mirror image (the reflection of the image through the `xy`-plane).

*Suggestion.* The right-handed trefoil is chiral. Parametrize it for
instance as

  `t ↦ (sin t + 2 sin (2 t), cos t − 2 cos (2 t), −sin (3 t))`.

Here chirality is understood in the orientation-sensitive sense induced by
the benchmark's notion of isotopy. Proving chirality therefore requires an
ambient-isotopy invariant that takes *different* values on a knot and its
mirror image. The figure-eight knot *is* isotopic to its mirror in the usual
unoriented sense, so the invariant must be sensitive to chirality — in
particular, the knot determinant and the Alexander polynomial alone do *not*
suffice (both are mirror-symmetric).

Standard chirality-detecting invariants:

* The **knot signature** `σ(K) ∈ ℤ`, computed from a Seifert matrix
  `V` as the signature of `V + Vᵀ`. Mirroring negates the signature, so
  any knot with `σ(K) ≠ 0` is chiral. The right-handed trefoil has
  `σ = −2`.
* The **Jones polynomial** `V_K(t) ∈ ℤ[t^{1/2}, t^{-1/2}]`. Mirroring
  sends `V_K(t)` to `V_K(t⁻¹)`, so any knot whose Jones polynomial is not
  symmetric under `t ↔ t⁻¹` is chiral. The right-handed trefoil has
  `V_K(t) = −t^{−4} + t^{−3} + t^{−1}`.

See <https://en.wikipedia.org/wiki/Chirality_(mathematics)> and
<https://en.wikipedia.org/wiki/Trefoil_knot>. -/
/-- **Existence of a chiral knot.** There exists an oriented smooth knot $K$ in $\mathbb{R}^3$
that is chiral: it is not ambient-isotopic, as an oriented knot, to its mirror image $r \circ K$,
where $r(x, y, z) = (x, y, -z)$ is the reflection through the $xy$-plane.

Source: Classical; see https://en.wikipedia.org/wiki/Chirality_(mathematics) and https://en.wikipedia.org/wiki/Trefoil_knot. Via leanprover/lean-eval@38361be, problem `exists_chiral_knot`. -/
public theorem_wanted exists_chiral_knot : ∃ K : Knot, K.Chiral

end KnotTheory

end MathlibExt.Topology.ChiralWanted
