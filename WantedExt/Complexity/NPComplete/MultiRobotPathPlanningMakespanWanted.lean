/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTI-ROBOT PATH PLANNING with bounded makespan is NP-complete

Source:
P. Surynek, "An optimization variant of multi-robot path planning is intractable",
Proceedings of the Twenty-Fourth AAAI Conference on Artificial Intelligence (AAAI 2010),
1261-1263, doi:10.1609/aaai.v24i1.7767.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultiRobotPathPlanningMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiRobotPathPlanningMakespan

/-!
# MULTI-ROBOT PATH PLANNING with bounded makespan is NP-complete

Also known as multi-agent path finding with optimal makespan (MAPF). Surynek (2010),
Definition 1: an undirected graph `G = (V, E)`, robots `R = {r₁, ..., r_ν}` with `ν < |V|`, an
initial arrangement `S⁰ : R → V` and a goal arrangement `S⁺ : R → V`, both simple (injective).
A solution of makespan `ζ` is a sequence `S⁰, S¹, ..., S^ζ` of simple arrangements with
(i) `S^ζ = S⁺`; (ii) at each step every robot stays (`S^{k+1}(r) = S^k(r)`) or moves along an
edge (`{S^k(r), S^{k+1}(r)} ∈ E`); (iii) every move is allowed, where allowed moves are defined
transitively: a move into a vertex that no other robot occupies at time `k` is allowed, and a
move into a vertex that another robot leaves at time `k` by an allowed move is allowed (robots
move like a train). QUESTION (the decision version of the optimization variant): given a bound
`T`, is there a solution of makespan at most `T`?

`Allowed` is an inductive predicate, the least set of moves closed under the two clauses of
(iii), so a rotation of robots along a cycle (in particular two robots swapping along an edge)
is not allowed. Since a robot may stay put, a solution of makespan `ζ ≤ T` extends to one of
makespan exactly `T`, so "at most `T`" and the source's "of the makespan `η`" agree. The source
writes condition (ii) for `k = 1, 2, ..., ζ - 1`; we impose it at every step `k < ζ`, starting
from `S⁰`, as its sequence `S⁰, ..., S^ζ` requires.

Vertices are `Fin n` and the graph is `Cslib.Complexity.Karp.edgeGraph n E`; robot `r` is the
`r`-th listed (start, goal) pair.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTI-ROBOT PATH PLANNING with bounded makespan is NP-complete.** Source: Surynek (2010),
Theorem 1 and the membership argument that follows it. -/
public theorem_wanted multiRobotPathPlanningMakespan_npComplete :
    multiRobotPathPlanningMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiRobotPathPlanningMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultiRobotPathPlanningMakespan
