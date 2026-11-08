/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bing's house with two rooms is contractible

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.HouseWithTwoRooms` — contractibleSpace_houseWithTwoRooms (manifest `manifests/problems/contractibleSpace_houseWithTwoRooms.toml`, rev 1, submitter Junyan Xu, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.HouseWithTwoRoomsWanted` namespace. Mathematical
statements are unchanged. Source: Allen Hatcher, *Algebraic Topology*.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section

namespace MathlibExt.Topology.HouseWithTwoRoomsWanted
namespace Topology

/-!
Bing's house with two rooms is contractible.

We use the construction on p.4 of Allen Hatcher, *Algebraic Topology*.
The three coordinate axes are horizontal, diagonal and vertical towards
the east, northeast and north directions respectively, with the origin
located at the southwest corner.
-/

open Set (Icc Ioo)

/-- Bing's house with two rooms (Hatcher's version) as a subspace of `ℝ × ℝ × ℝ`. -/
def HouseWithTwoRooms : Set (ℝ × ℝ × ℝ) :=
  (Icc 0 4 ×ˢ Icc 0 3 ×ˢ {0, 1, 2} \
    (Ioo 2 3 ×ˢ Ioo 1 2 ×ˢ {0} ∪ Ioo 1 3 ×ˢ Ioo 1 2 ×ˢ {1} ∪ Ioo 1 2 ×ˢ Ioo 1 2 ×ˢ {2})) ∪
  ({1} ×ˢ Icc 1 2 ×ˢ Icc 1 2 ∪ {2} ×ˢ Icc 1 3 ×ˢ Icc 0 2 ∪ {3} ×ˢ Icc 1 2 ×ˢ Icc 0 1 ∪
    Icc 1 2 ×ˢ {1, 2} ×ˢ Icc 1 2 ∪ Icc 2 3 ×ˢ {1, 2} ×ˢ Icc 0 1) ∪
  (Icc 0 4 ×ˢ {0, 3} ×ˢ Icc 0 2 ∪ {0, 4} ×ˢ Icc 0 3 ×ˢ Icc 0 2)

/-- Source: Allen Hatcher, *Algebraic Topology*. Via leanprover/lean-eval@38361be, problem `contractibleSpace_houseWithTwoRooms`. -/
public theorem_wanted contractibleSpace_houseWithTwoRooms : ContractibleSpace HouseWithTwoRooms

end Topology

end MathlibExt.Topology.HouseWithTwoRoomsWanted
