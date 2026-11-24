/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROUTING WITH MUST PAIRS is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide" (fifth edition), Journal of
Algorithms 3 (1982), 381-395, doi:10.1016/0196-6774(82)90032-3, problem [2] ROUTING WITH
"MUST PAIRS" (reference: Ntafos and Hakimi; transformation from 3SAT);
S. C. Ntafos and S. L. Hakimi, "On path cover problems in digraphs and applications to
program testing", IEEE Transactions on Software Engineering SE-5 (1979), 520-529,
doi:10.1109/TSE.1979.234213.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation
public import WantedExt.Complexity.NPComplete.PathWithForbiddenPairsWanted
public import WantedExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPathsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RoutingWithMustPairs

/-!
# ROUTING WITH MUST PAIRS is NP-complete

INSTANCE: an acyclic directed graph `G = (V, A)`, two specified vertices `s, t ∈ V`, and a
subset `M` of the transitive closure `A*` of `A`, whose elements are called must-pairs.
QUESTION: is there a path `P` in `G` from `s` to `t` such that for each must-pair
`(u, v) ∈ M`, if `P` passes through `u` then it also passes through `v`?

The instance has the shape of PATH WITH FORBIDDEN PAIRS ([GT54],
`PathWithForbiddenPairsWanted`), which the column names as the related problem: vertex count
`n` (vertices `0, ..., n - 1`), arc list `A`, `s`, `t`, and a list of vertex pairs, here the
must-pairs. The instance type and `PathWithForbiddenPairs.WellFormed` (arcs, `s`, `t` and
pairs use vertices below `n`) are reused; `WellFormed` adds the two conditions the column puts
in the instance:

* acyclic: no vertex reaches itself along one or more arcs (`Relation.TransGen`, as in
  `PathWithDisjointForbiddenPairsWanted`);
* every must-pair `(u, v)` lies in the transitive closure: `v` is reachable from `u` along one
  or more arcs.

A path from `s` to `t` is `DirectedTwoDisjointConnectingPaths.IsDirectedPath`: a vertex list
starting at `s`, ending at `t`, without repeated vertices, consecutive vertices joined by an
arc. In an acyclic digraph every walk is such a path. "`P` passes through `u`" is membership
of `u` in the list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (arcs, `s`, `t` and must-pairs use vertices
below `n`), the digraph is acyclic, and every must-pair `(u, v)` is in the transitive closure
of the arcs. -/
def WellFormed (i : PathWithForbiddenPairs.PathWithForbiddenPairsInstance) : Prop :=
  PathWithForbiddenPairs.WellFormed i ∧
    (∀ v, ¬ Relation.TransGen (fun u w => (u, w) ∈ i.2.1) v v) ∧
    ∀ m ∈ i.2.2.2.2, Relation.TransGen (fun u w => (u, w) ∈ i.2.1) m.1 m.2

/-- Some path `P` from `s` to `t` passes through `v` whenever it passes through `u`, for every
must-pair `(u, v)`. -/
def RoutingWithMustPairsFeasible
    (i : PathWithForbiddenPairs.PathWithForbiddenPairsInstance) : Prop :=
  ∃ p : List ℕ, DirectedTwoDisjointConnectingPaths.IsDirectedPath i.2.1 i.2.2.1 i.2.2.2.1 p ∧
    ∀ m ∈ i.2.2.2.2, m.1 ∈ p → m.2 ∈ p

open Classical in
/-- ROUTING WITH MUST PAIRS as a decision problem over bitstrings. -/
noncomputable def routingWithMustPairsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathWithForbiddenPairs.PathWithForbiddenPairsInstance) x with
  | some i => decide (WellFormed i ∧ RoutingWithMustPairsFeasible i)
  | none => false

/-- **ROUTING WITH MUST PAIRS is NP-complete.** Source: Johnson, NP-completeness column (1982),
problem [2]; Ntafos and Hakimi (1979). -/
public theorem_wanted routingWithMustPairs_npComplete :
    routingWithMustPairsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L routingWithMustPairsDec

end MetaMathlibExt.Complexity.NPComplete.RoutingWithMustPairs
