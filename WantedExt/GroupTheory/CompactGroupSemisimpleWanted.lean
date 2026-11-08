/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Complete reducibility for compact groups

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.RepresentationTheory.CompactGroupSemisimple` — compact_group_semisimple (manifest `manifests/problems/compact_group_semisimple.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.CompactGroupSemisimpleWanted` namespace. Mathematical
statements are unchanged. Source: H. Weyl, *Theorie der Darstellung kontinuierlicher halb-einfacher Gruppen durch lineare Transformationen* (1925–26); Peter–Weyl (1927). Knill, *Some fundamental theorems in mathematics*, §21.
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.RepresentationTheory.Semisimple

@[expose] public section

namespace MathlibExt.GroupTheory.CompactGroupSemisimpleWanted
namespace RepresentationTheory.CompactGroupSemisimple

/-!
# Complete reducibility for compact groups

`compact_group_semisimple`: a continuous representation of a compact topological
group on a finite-dimensional real vector space is semisimple (every
subrepresentation has a `G`-invariant complement). This is the unitarian trick:
averaging an inner product over Haar measure produces a `G`-invariant inner
product. Mathlib has `IsSemisimpleRepresentation` and Maschke's theorem (finite
groups) but no compact-group / Peter–Weyl result. Category-(b) candidate from
§21 of the Knill survey.
-/

open Representation

/- **Representations of compact groups are semisimple** (complete
reducibility / the unitarian trick). A continuous representation of a compact
topological group on a finite-dimensional real vector space is semisimple:
every subrepresentation has a `G`-invariant complement, so the representation
decomposes as a direct sum of irreducible finite-dimensional
subrepresentations. -/
/-- Source: H. Weyl, *Theorie der Darstellung kontinuierlicher halb-einfacher Gruppen durch lineare Transformationen* (1925–26); Peter–Weyl (1927). Knill, *Some fundamental theorems in mathematics*, §21. Via leanprover/lean-eval@38361be, problem `compact_group_semisimple`. -/
public theorem_wanted compact_group_semisimple
    {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : Representation ℝ G V)
    (hρ : Continuous fun p : G × V => ρ p.1 p.2) :
    ρ.IsSemisimpleRepresentation

end RepresentationTheory.CompactGroupSemisimple

end MathlibExt.GroupTheory.CompactGroupSemisimpleWanted
