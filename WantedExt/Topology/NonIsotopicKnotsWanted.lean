/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Existence of a non-isotopic pair of oriented knots

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.KnotTheory.NonIsotopicKnots` — exists_nonisotopic_knots (manifest `manifests/problems/exists_nonisotopic_knots.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.NonIsotopicKnotsWanted` namespace. The shared knot-theory prelude is imported from `WantedExt.Topology.ConwayKnotShared` instead of being copied here. Mathematical
statements are unchanged. Source: Classical; see https://en.wikipedia.org/wiki/Knot_invariant.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.ConwayKnotShared
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace MathlibExt.Topology.NonIsotopicKnotsWanted
namespace KnotTheory

open MathlibExt.Topology.ConwayKnotShared.KnotTheory

/-! The knot-theory model (`R3`, `Knot`, `TwoLink`, `AmbientIsotopy`,
`CircleReparam`, isotopy, `reflectZ`, chirality) is shared with the other
knot entries via `WantedExt.Topology.ConwayKnotShared` and is not copied
here, so all knot entries speak about the same `Knot` type. -/

/-!
# Existence of non-isotopic knots

Distinguishing two knots is genuinely harder than distinguishing two links:
no `lk`-style integral does the job, so any proof has to construct an
ambient-isotopy invariant of single-component knots and compute it on two
explicit parametrizations.
-/

/- **Existence of a non-isotopic pair of oriented smooth knots.**

There exist two oriented smooth knots in `ℝ³` that are not ambient-isotopic.

*Suggestion.* Take `K₁` to be the **unknot**, parametrized as the round
unit circle in the `xy`-plane, and `K₂` to be the **right-handed trefoil**,
parametrized for instance by

  `t ↦ (sin t + 2 sin (2 t), cos t − 2 cos (2 t), −sin (3 t))`

(this is a smooth, 2π-periodic immersion, and it is injective on `[0, 2π)`).

To distinguish them, you must construct an ambient-isotopy invariant of
knots. Two computationally tractable options, each fully developed from
elementary ingredients:

* The **knot determinant** `|Δ_K(−1)|`, where `Δ_K ∈ ℤ[t, t⁻¹]` is the
  Alexander polynomial. The unknot has determinant `1`; the trefoil has
  determinant `3`.
* The number of **Fox 3-colorings** of any diagram of `K`, which counts
  homomorphisms from the knot group to the dihedral group `D₃` and is an
  isotopy invariant. The unknot admits only monochromatic 3-colorings
  (3 of them); the trefoil admits 9.

See <https://en.wikipedia.org/wiki/Knot_invariant> for a survey. -/
/-- Source: Classical; see https://en.wikipedia.org/wiki/Knot_invariant. Via leanprover/lean-eval@38361be, problem `exists_nonisotopic_knots`. -/
public theorem_wanted exists_nonisotopic_knots : ∃ K₁ K₂ : Knot, ¬ K₁.Isotopic K₂

end KnotTheory

end MathlibExt.Topology.NonIsotopicKnotsWanted
