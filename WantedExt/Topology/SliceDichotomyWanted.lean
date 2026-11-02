/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Existence of a topologically slice, not smoothly slice knot

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.KnotTheory.SliceDichotomy` — exists_topologically_slice_not_smoothly_slice (manifest `manifests/problems/exists_topologically_slice_not_smoothly_slice.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.SliceDichotomyWanted` namespace. The shared knot-theory prelude is imported from `WantedExt.Topology.ConwayKnotShared` instead of being copied here. Mathematical
statements are unchanged. Source: Casson, 1980s (unpublished); Akbulut-Matveyev, *A convex decomposition theorem for 4-manifolds*, IMRN 1998. See also Hedden-Kirk-Livingston, *Non-slice linear combinations of algebraic knots*, J. Eur. Math. Soc. 14 (2012).
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.ConwayKnotShared
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace MathlibExt.Topology.SliceDichotomyWanted
namespace KnotTheory

open MathlibExt.Topology.ConwayKnotShared.KnotTheory

/-! The knot-theory model (`R3`, `Knot`, `TwoLink`, `AmbientIsotopy`,
`CircleReparam`, isotopy, `reflectZ`, chirality) is shared with the other
knot entries via `WantedExt.Topology.ConwayKnotShared` and is not copied
here, so all knot entries speak about the same `Knot` type. -/

/-!
# Existence of a topologically slice, not smoothly slice knot

The Casson / Akbulut–Matveyev / Hedden–Kirk–Livingston dichotomy in
dimension four: there exist knots in `S³` that bound a locally flat
topological disk in the 4-ball but no smoothly embedded one. This problem
asks only for some such knot; the celebrated specific witness — the
Conway knot 11n34 — is the subject of `Piccirillo` and
`ConwayTopologicallySlice`.

Rasmussen's `s`-invariant and the Ozsváth–Szabó `τ`-invariant obstruct
*smooth* sliceness: `s(K) ≠ 0` (or `τ(K) ≠ 0`) implies `K` is not
smoothly slice. Topologically slice knots can perfectly well have
nonzero `s` and `τ` — which is exactly how witnesses to this dichotomy
are detected. The easiest historical example is the positive Whitehead
double of the right-handed trefoil: trivial Alexander polynomial gives
topological sliceness by Freedman, and `τ ≠ 0` rules out smooth
sliceness (Akbulut–Matveyev).
-/

/- **Existence of a topologically slice, not smoothly slice knot.**

There exists a piecewise-linear knot in `ℝ³` that bounds a locally flat
topological 2-disk in `ℝ³ × [0, ∞)` but no smoothly properly embedded
2-disk in `ℝ³ × [0, ∞)`.

This was first established by Casson; explicit examples were given by
Akbulut–Matveyev and Hedden–Kirk–Livingston. The solver may take any
witness — historically tractable ones are positive Whitehead doubles
of certain knots (Akbulut–Matveyev, 1997). -/
/-- **A topologically slice knot that is not smoothly slice.** There is a PL knot $K$ (a closed
polyline in $\mathbb{R}^3$ with at least three vertices, not required to be simple) that is
topologically slice but not smoothly slice. Here $K$ is smoothly (respectively topologically)
slice when some smooth knot whose image is topologically ambient isotopic to the image of $K$
bounds a smooth (respectively locally flat) properly embedded $2$-disk in
$\mathbb{R}^3 \times [0, \infty)$.

Source: Casson, 1980s (unpublished); Akbulut-Matveyev, *A convex decomposition theorem for 4-manifolds*, IMRN 1998. See also Hedden-Kirk-Livingston, *Non-slice linear combinations of algebraic knots*, J. Eur. Math. Soc. 14 (2012). Via leanprover/lean-eval@38361be, problem `exists_topologically_slice_not_smoothly_slice`. -/
public theorem_wanted exists_topologically_slice_not_smoothly_slice :
    ∃ K : PLKnot, K.TopologicallySlice ∧ ¬ K.SmoothlySlice

end KnotTheory

end MathlibExt.Topology.SliceDichotomyWanted
