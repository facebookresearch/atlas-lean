/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nikolov–Segal strong completeness theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.NikolovSegal` — nikolov_segal (manifest `manifests/problems/nikolov_segal.toml`, rev 1, submitter Adam Topaz, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.NikolovSegalWanted` namespace. Mathematical
statements are unchanged. Source: Nikolay Nikolov and Dan Segal, *On finitely generated profinite groups, I: strong completeness and uniform bounds*, Annals of Mathematics 165 (2007), no. 1, 171–238, Theorem 1.1, https://doi.org/10.4007/annals.2007.165.171; *On finitely generated profinite groups, II: products in quasisimple groups*, Annals of Mathematics 165 (2007), no. 1, 239–273, https://doi.org/10.4007/annals.2007.165.239.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Topology.Algebra.StrongCompleteness
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.NikolovSegalWanted
namespace GroupTheory

/-!
# Nikolov–Segal strong completeness theorem

A profinite group is **strongly complete** when all of its finite-index subgroups are open.
Nikolov and Segal proved that every topologically finitely generated profinite group is strongly
complete. In particular, its topology is determined by its underlying abstract group structure.

## References

* [Nikolov and Segal, *On finitely generated profinite groups, I: strong completeness and uniform
  bounds*](https://doi.org/10.4007/annals.2007.165.171), Theorem 1.1.
* [Nikolov and Segal, *On finitely generated profinite groups, II: products in quasisimple
  groups*](https://doi.org/10.4007/annals.2007.165.239).
-/

/-- A topological group is topologically finitely generated if some finite set generates a dense
abstract subgroup. -/
def IsTopologicallyFinitelyGenerated
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∃ S : Finset G, (Subgroup.closure (S : Set G)).topologicalClosure = ⊤

/-- **Nikolov–Segal strong completeness theorem.** Every finite-index subgroup of a
topologically finitely generated profinite group is open.

Source: Nikolay Nikolov and Dan Segal, *On finitely generated profinite groups, I:
strong completeness and uniform bounds*, Annals of Mathematics 165 (2007), no. 1,
171–238, Theorem 1.1, https://doi.org/10.4007/annals.2007.165.171;
*On finitely generated profinite groups, II: products in quasisimple groups*,
Annals of Mathematics 165 (2007), no. 1, 239–273, https://doi.org/10.4007/annals.2007.165.239.
Via leanprover/lean-eval@38361be, problem `nikolov_segal`. -/
public theorem_wanted nikolov_segal
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsTopologicallyFinitelyGenerated G) :
    IsStronglyComplete G

end GroupTheory

end MathlibExt.GroupTheory.NikolovSegalWanted
