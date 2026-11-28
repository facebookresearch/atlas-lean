/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE CONSTRAINED SCHEDULING with two processors, chains and a unit resource is NP-complete

Source:
J. Błażewicz, J. K. Lenstra and A. H. G. Rinnooy Kan, "Scheduling subject to resource constraints:
classification and complexity", Discrete Applied Mathematics 5 (1983), 11-24,
doi:10.1016/0166-218X(83)90012-4, Theorem 7 ("P2|res111, chain, p_j = 1|C_max is NP-hard in the
strong sense", by a transformation from 3-PARTITION; read in the Mathematisch Centrum preprint
BW 127/80 of the same title);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS10] RESOURCE CONSTRAINED SCHEDULING.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ResourceConstrainedSchedulingChainsUnitResourceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingChainsUnitResource

open MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedScheduling (bound)
open MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingPrecedenceZeroOrBound
  (PrecedenceResourceSchedulingInstance PrecedenceWellFormed PrecedenceFeasible)
open MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingForestPrecedence
  (ImmediatePredecessor)

/-!
# RESOURCE CONSTRAINED SCHEDULING with two processors, chains and a unit resource is NP-complete

The problem `P2 | res111, chain, p_j = 1 | C_max` of Błażewicz, Lenstra and Rinnooy Kan, as a
decision problem with a deadline. INSTANCE: a set `T` of tasks, each having length `l(t) = 1`,
`m = 2` processors, one resource of size `B_1 = 1`, a requirement `R_1(t) ∈ {0, 1}` for each task
`t`, chain-like precedence constraints, and a deadline `D ∈ ℤ⁺`. QUESTION: is there a
`2`-processor schedule `σ` that meets the deadline `D`, obeys the precedence constraints (`t`
before `t'` implies `σ(t') ≥ σ(t) + 1`) and obeys the resource constraint (at every time the
running tasks require at most `B_1 = 1` in total)?

In the source the precedence constraints are a directed acyclic graph `H`, a job preceding every
job it reaches by a directed path, and they are chain-like when `H` has both outdegree and
indegree at most one at every vertex; `res111` means one resource, of size `1`, with every
requirement at most `1`. The instance, the well-formedness of RESOURCE CONSTRAINED SCHEDULING with
a partial order (the listed pairs are the whole strict order, i.e. the pairs connected by a path
of `H`) and the question are `PrecedenceResourceSchedulingInstance`, `PrecedenceWellFormed` and
`PrecedenceFeasible` of `ResourceConstrainedSchedulingPrecedenceZeroOrBoundWanted`; the
requirement bound `R_1(t) ≤ B_1` there makes every requirement `0` or `1`. A graph with indegree
and outdegree at most one has no arc implied by two others, so `H` is the immediate-predecessor
relation of the order (`ImmediatePredecessor` of
`ResourceConstrainedSchedulingForestPrecedenceWanted`, whose forests have only one of the two
degree bounds), and the order is a set of chains when every task has at most one immediate
successor and at most one immediate predecessor. Numbers use the binary encoding (the problem is
NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RESOURCE CONSTRAINED SCHEDULING with two processors, chains and a unit resource is
NP-complete.** Source: Błażewicz, Lenstra and Rinnooy Kan (1983), Theorem 7; Garey and Johnson
(1979), [SS10]. -/
public theorem_wanted resourceConstrainedSchedulingChainsUnitResource_npComplete :
    resourceConstrainedSchedulingChainsUnitResourceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L resourceConstrainedSchedulingChainsUnitResourceDec

end MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingChainsUnitResource
