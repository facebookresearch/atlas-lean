/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Conway knot is not smoothly slice

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.KnotTheory.Piccirillo` — conway_knot_not_smoothly_slice (manifest `manifests/problems/conway_knot_not_smoothly_slice.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.PiccirilloWanted` namespace. Mathematical
statements are unchanged. Source: https://arxiv.org/abs/1808.02923
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.ConwayKnotShared
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace MathlibExt.Topology.PiccirilloWanted

namespace KnotTheory
open MathlibExt.Topology.ConwayKnotShared.KnotTheory

/-!
# The Conway knot is not smoothly slice

Lisa Piccirillo, *The Conway knot is not slice* (Annals of Mathematics,
2020; arXiv 1808.02923). Piccirillo resolved the last remaining case in
the classification of slice knots through 12 crossings by showing the
Conway knot 11n34 is not smoothly slice. Combined with
`ConwayTopologicallySlice`, this is a celebrated small witness in the
smooth/topological slice gap (earlier explicit witnesses such as the
Akbulut–Matveyev positive Whitehead doubles existed; Conway is notable
for its low crossing number and its history as a long-standing open case).

Piccirillo's strategy: exhibit a knot `K'` having the same `0`-trace as
the Conway knot. The trace-embedding argument then transfers sliceness:
if the Conway knot were smoothly slice, `K'` would be smoothly slice as
well. A direct Khovanov-homological computation shows Rasmussen's
`s`-invariant satisfies `s(K') ≠ 0`, contradicting smooth sliceness of
`K'`. Note that for the Conway knot itself the standard smooth slice
obstructions `s` and `τ` both vanish, which is why this trace-embedding
detour through `K'` is needed.
-/

/- **The Conway-knot polyline is a simple closed curve.**

A finite — if laborious — check on the fixed 78-vertex braid-closure
polyline: all vertices distinct, non-adjacent edges disjoint, adjacent
edges meeting only at their shared vertex. This certifies that `conwayKnot`
is a genuine embedded knot — the subject the slice question is about — and
is posed as its own hole so that the proof lives in the submission rather
than as an unchecked field of `conwayKnot`. -/
/-- **The Conway knot polyline is a simple closed curve.** Let $K$ be the Conway knot $11n34$,
realized as a closed polyline in $\mathbb{R}^3$ (the braid closure of a 4-strand braid word for
it), and let $N$ be its number of vertices. The periodic piecewise-linear parametrization of $K$,
which traverses each edge in unit time, is injective on the interval $[0, N)$.

Equivalently, the vertices of $K$ are distinct, non-adjacent edges are disjoint, and adjacent
edges meet only at their shared vertex.

Source: https://arxiv.org/abs/1808.02923 Via leanprover/lean-eval@38361be, problem `conway_knot_not_smoothly_slice`. -/
public theorem_wanted conwayKnot_isSimple : conwayKnot.IsSimple

/- **Piccirillo, "The Conway knot is not slice."**

The Conway knot 11n34 does not bound a smoothly properly embedded 2-disk
in `ℝ³ × [0, ∞)`. -/
/-- **The Conway knot is not smoothly slice (Piccirillo).** Let $K$ be the Conway knot $11n34$,
realized as a closed polyline in $\mathbb{R}^3$. There is no smooth knot $J$, that is, a smooth
$2\pi$-periodic map $\mathbb{R} \to \mathbb{R}^3$ with nowhere vanishing derivative that is
injective on $[0, 2\pi)$, with both of the following properties: some topological ambient isotopy
of $\mathbb{R}^3$ carries the image of $J$ onto the image of $K$; and there is a smooth map
$D \colon \mathbb{R}^2 \to \mathbb{R}^3 \times \mathbb{R}$ that is injective with injective
derivative on the closed unit disk $\overline{\mathbb{D}}$, takes $\overline{\mathbb{D}}$ into the
half-space $\mathbb{R}^3 \times [0, \infty)$, takes a point of $\overline{\mathbb{D}}$ to height
$0$ exactly when it lies on the unit circle, and whose $\mathbb{R}^3$-component maps the unit
circle onto the image of $J$.

Source: https://arxiv.org/abs/1808.02923 Via leanprover/lean-eval@38361be, problem `conway_knot_not_smoothly_slice`. -/
public theorem_wanted conway_knot_not_smoothly_slice : ¬ conwayKnot.SmoothlySlice

end KnotTheory

end MathlibExt.Topology.PiccirilloWanted
