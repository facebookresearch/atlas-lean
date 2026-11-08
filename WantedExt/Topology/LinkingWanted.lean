/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Existence of a non-isotopic pair of oriented two-component links

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.KnotTheory.Linking` — exists_nonisotopic_link (manifest `manifests/problems/exists_nonisotopic_link.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.LinkingWanted` namespace. The shared knot-theory prelude is imported from `WantedExt.Topology.ConwayKnotShared` instead of being copied here. Mathematical
statements are unchanged. Source: Classical; see https://en.wikipedia.org/wiki/Linking_number.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.ConwayKnotShared
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace MathlibExt.Topology.LinkingWanted
namespace KnotTheory

open MathlibExt.Topology.ConwayKnotShared.KnotTheory

/-! The knot-theory model (`R3`, `Knot`, `TwoLink`, `AmbientIsotopy`,
`CircleReparam`, isotopy, `reflectZ`, chirality) is shared with the other
knot entries via `WantedExt.Topology.ConwayKnotShared` and is not copied
here, so all knot entries speak about the same `Knot` type. -/

/-!
# Existence of non-isotopic two-component links

A warmup for the knot-theory benchmark. Two-component links are easier to
distinguish than knots because the *Gauss linking integral* is a real-valued
ambient-isotopy invariant defined by an explicit double integral over the
two parametrizations — no diagrammatic machinery needed.
-/

/- **Existence of a non-isotopic pair of oriented two-component links.**

There exist two oriented smooth two-component links in `ℝ³` that are not
ambient-isotopic.

*Suggestion.* Take `L₁` to be the **unlink** — for instance, the two unit
circles in the planes `z = 0` and `z = 2`, both centered on the `z`-axis —
and `L₂` to be the **Hopf link** — for instance, the unit circle in the
`xy`-plane together with the unit circle in the `xz`-plane shifted by `(1, 0, 0)`.

To distinguish them, use the **Gauss linking integral**

  `lk(K, L) = (1 / (4π)) ∫₀^{2π} ∫₀^{2π}`
              `⟨K(s) − L(t), K′(s) × L′(t)⟩ / ‖K(s) − L(t)‖³ ds dt`,

which is well-defined when the components have disjoint images, takes the
value `0` on the unlink and `±1` on the Hopf link depending on the chosen
orientations, and is invariant under ambient isotopy of the oriented link.
(Invariance follows from a Stokes-style computation: the integrand is the
pullback of a closed 2-form on `ℝ³ \ {0}`.)

See <https://en.wikipedia.org/wiki/Linking_number> for a reference. -/
/-- Source: Classical; see https://en.wikipedia.org/wiki/Linking_number. Via leanprover/lean-eval@38361be, problem `exists_nonisotopic_link`. -/
public theorem_wanted exists_nonisotopic_link : ∃ L₁ L₂ : TwoLink, ¬ L₁.Isotopic L₂

end KnotTheory

end MathlibExt.Topology.LinkingWanted
