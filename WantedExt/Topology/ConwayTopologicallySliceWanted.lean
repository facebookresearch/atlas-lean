/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Conway knot is topologically slice

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.KnotTheory.ConwayTopologicallySlice` — conway_knot_topologically_slice (manifest `manifests/problems/conway_knot_topologically_slice.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.ConwayTopologicallySliceWanted` namespace. Mathematical
statements are unchanged. Source: Freedman, *The topology of four-dimensional manifolds*, J. Diff. Geom. 17 (1982). See also Freedman-Quinn, *Topology of 4-Manifolds*, Princeton 1990.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.ConwayKnotShared
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace MathlibExt.Topology.ConwayTopologicallySliceWanted

namespace KnotTheory
open MathlibExt.Topology.ConwayKnotShared.KnotTheory

/-!
# The Conway knot is topologically slice

A direct application of Freedman's theorem: every knot in `S³` whose
Alexander polynomial is trivial bounds a locally flat topological 2-disk
in `B⁴`. The Conway knot 11n34 has `Δ_K(t) = 1`, so it is topologically
slice. The proof requires Freedman's full machinery (topological surgery
in dimension four); this is a hard problem.
-/

/- **The Conway knot is topologically slice.**

Freedman (1982): every knot with trivial Alexander polynomial bounds a
locally flat topological disk in the 4-ball. The Conway knot has
`Δ_K(t) = 1`, so applying this theorem yields a locally flat topological
slice disk. -/
/-- Source: Freedman, *The topology of four-dimensional manifolds*, J. Diff. Geom. 17 (1982). See also Freedman-Quinn, *Topology of 4-Manifolds*, Princeton 1990. Via leanprover/lean-eval@38361be, problem `conway_knot_topologically_slice`. -/
public theorem_wanted conway_knot_topologically_slice : conwayKnot.TopologicallySlice

end KnotTheory

end MathlibExt.Topology.ConwayTopologicallySliceWanted
