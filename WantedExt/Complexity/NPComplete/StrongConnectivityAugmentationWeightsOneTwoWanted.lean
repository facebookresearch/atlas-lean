/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRONG CONNECTIVITY AUGMENTATION with weights 1 or 2 and no arcs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND19] STRONG CONNECTIVITY
AUGMENTATION, comment on p. 211 ("Remains NP-complete if all weights are either 1 or 2 and A is
empty");
K. P. Eswaran and R. E. Tarjan, "Augmentation problems", SIAM Journal on Computing 5 (1976),
653-665, doi:10.1137/0205044.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.StrongConnectivityAugmentationWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StrongConnectivityAugmentationWeightsOneTwo

open MetaMathlibExt.Complexity.NPComplete.StrongConnectivityAugmentation
  (StrongConnectivityAugmentationInstance weight StrongConnectivityAugmentationFeasible)

/-!
# STRONG CONNECTIVITY AUGMENTATION with weights 1 or 2 and no arcs is NP-complete

INSTANCE: a directed graph `G = (V, A)` with `A` empty, a weight `w(u, v) ∈ {1, 2}` for each
ordered pair `(u, v) ∈ V × V`, and a positive integer `B`.
QUESTION: is there a set `A'` of ordered pairs of vertices from `V` such that
`∑_{a ∈ A'} w(a) ≤ B` and the graph `G' = (V, A ∪ A')` is strongly connected?

The instance and the question are those of STRONG CONNECTIVITY AUGMENTATION
(`WantedExt.Complexity.NPComplete.StrongConnectivityAugmentationWanted`: vertices
`0, ..., n - 1`, the arc list of `G`, an `n × n` matrix of positive weights, and the bound
`B > 0`; the question asks for a list `A'` of ordered pairs whose total weight is at most `B` and
whose addition to `G` makes every vertex reach every vertex). The restriction adds that the arc
list of `G` is empty and that every weight `w(u, v)`, `u, v < n`, is `1` or `2`.

Garey and Johnson record this restriction in the entry whose reference is Eswaran and Tarjan
(1976), a transformation from HAMILTONIAN CIRCUIT. It is consistent with directed HAMILTONIAN
CIRCUIT (Karp 1972): give the arcs of a digraph `H` on `|V| ≥ 2` vertices weight `1`, every
other ordered pair weight `2`, and take `B = |V|`. A strongly connected `G'` gives every vertex
an arc to another vertex, so `A'` has weight at least `|V|`, with equality only when it consists
of `|V|` arcs of `H`, one leaving each vertex, which then form a Hamiltonian circuit. Membership
in NP is inherited: the certificate is `A'` without repeated pairs (at most `|V|²` pairs),
and strong connectivity is checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed STRONG CONNECTIVITY AUGMENTATION instance
with no arcs in `G` and every weight equal to `1` or `2`. -/
def WellFormed (i : StrongConnectivityAugmentationInstance) : Prop :=
  StrongConnectivityAugmentation.WellFormed i ∧ i.2.1 = [] ∧
    ∀ u < i.1, ∀ v < i.1, weight i.2.2.1 u v = 1 ∨ weight i.2.2.1 u v = 2

open Classical in
/-- STRONG CONNECTIVITY AUGMENTATION with weights 1 or 2 and no arcs as a decision problem over
bitstrings. -/
noncomputable def strongConnectivityAugmentationWeightsOneTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StrongConnectivityAugmentationInstance) x with
  | some i => decide (WellFormed i ∧ StrongConnectivityAugmentationFeasible i)
  | none => false

/-- **STRONG CONNECTIVITY AUGMENTATION with weights 1 or 2 and no arcs is NP-complete.**
Source: Garey and Johnson (1979), [ND19]; Eswaran and Tarjan (1976). -/
public theorem_wanted strongConnectivityAugmentationWeightsOneTwo_npComplete :
    strongConnectivityAugmentationWeightsOneTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L strongConnectivityAugmentationWeightsOneTwoDec

end MetaMathlibExt.Complexity.NPComplete.StrongConnectivityAugmentationWeightsOneTwo
