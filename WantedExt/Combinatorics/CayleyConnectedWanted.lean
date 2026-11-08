/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cayley graph connected iff generators generate the group

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.CayleyConnected` — mulCayley_connected_iff_closure_eq_top (manifest `manifests/problems/mulCayley_connected_iff_closure_eq_top.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.CayleyConnectedWanted` namespace. Mathematical
statements are unchanged. Source: A. Cayley, On the theory of groups, as depending on the symbolic equation θ^n = 1, 1878.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Algebra.Group.Subgroup.Lattice

@[expose] public section

namespace MathlibExt.Combinatorics.CayleyConnectedWanted
namespace Combinatorics

/-!
A Cayley graph is connected if and only if its generators generate the group.

The Cayley graph of a group `G` with generators `S` has vertex set `G` and an edge between
`x` and `y` whenever `x * g = y` for some `g ∈ S`. This theorem characterises connectivity:
the Cayley graph is connected if and only if `S` generates `G` as a group. The forward
direction constructs a path from `1` to any `g ∈ G` via the generators; the reverse shows
that any path in the graph corresponds to a product of generators.

This is a foundational result in geometric group theory, connecting algebraic generation
to graph-theoretic connectivity.
-/

public theorem_wanted mulCayley_connected_iff_closure_eq_top
    {G : Type*} [Group G]
    (S : Set G) :
    (SimpleGraph.mulCayley S).Connected ↔ Subgroup.closure S = ⊤

end Combinatorics

end MathlibExt.Combinatorics.CayleyConnectedWanted
