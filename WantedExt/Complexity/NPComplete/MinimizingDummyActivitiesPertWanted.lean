/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMIZING DUMMY ACTIVITIES IN PERT NETWORKS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND44] MINIMIZING DUMMY ACTIVITIES IN
PERT NETWORKS, p. 218;
M. S. Krishnamoorthy and N. Deo, "Complexity of the minimum-dummy-activities problem in a PERT
network", Networks 9 (1979), 189-194, doi:10.1002/net.3230090302.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimizingDummyActivitiesPertDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimizingDummyActivitiesPert

/-!
# MINIMIZING DUMMY ACTIVITIES IN PERT NETWORKS is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)`, where vertices represent tasks and the arcs
represent precedence constraints, and a positive integer `K ≤ |V|`. QUESTION: is there a PERT
network corresponding to `G` with `K` or fewer dummy activities, i.e., a directed acyclic graph
`G' = (V', A')` where `V' = {vᵢ⁻, vᵢ⁺ : vᵢ ∈ V}` and `{(vᵢ⁻, vᵢ⁺) : vᵢ ∈ V} ⊆ A'`, such that
`|A'| ≤ |V| + K` and such that there is a path from `vᵢ⁺` to `vⱼ⁻` in `G'` if and only if there
is a path from `vᵢ` to `vⱼ` in `G`?

`G` is a Mathlib `Digraph (Fin n)` given by its arc list. In a PERT (activity-on-arc) network
the end of one activity and the start of another may be the same event, so the names `vᵢ⁻`,
`vᵢ⁺` need not denote distinct vertices: `G'` has events `Fin m`, every event is one of the
names (`V' = {vᵢ⁻, vᵢ⁺}`), and task `vᵢ` is the arc from `tail i = vᵢ⁻` to `head i = vᵢ⁺`. The
task arcs are distinct (one activity per arc), the arcs of `A'` other than the task arcs are the
dummy activities, and `|A'| ≤ |V| + K` says there are at most `K` of them. A path in `G'` from
`vᵢ⁺` to `vⱼ⁻` may be empty (when `vᵢ⁺` and `vⱼ⁻` are the same event; `ReflTransGen`), while a
path from `vᵢ` to `vⱼ` in `G` is a nonempty directed path (`TransGen`): for `i = j`, `G` has
no such path (it is acyclic) and neither has `G'`, since `vᵢ⁺ ⇝ vᵢ⁻` would close a cycle with the
task arc.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMIZING DUMMY ACTIVITIES IN PERT NETWORKS is NP-complete.** Source: Garey and Johnson
(1979), [ND44]; Krishnamoorthy and Deo (1979). -/
public theorem_wanted minimizingDummyActivities_npComplete :
    minimizingDummyActivitiesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimizingDummyActivitiesDec

end MetaMathlibExt.Complexity.NPComplete.MinimizingDummyActivitiesPert
