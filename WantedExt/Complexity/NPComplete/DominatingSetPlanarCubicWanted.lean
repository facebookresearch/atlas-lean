/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on planar cubic graphs is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 5 (1984), 147-160,
doi:10.1016/0196-6774(84)90045-2, Section 3, DOMINATING SET [GT2]: the class for which
NP-completeness was proved is "3-regular planar graphs" (Garey and Johnson, unpublished result
(1978) cited in [G&J]; proved independently by T. Kikuno and Y. Kakuda, "The NP-completeness of
the dominating set problem in cubic planar graphs", manuscript (1979)), correcting the
"planar graphs that are regular of degree 4" of the [GT2] comment;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DominatingSetPlanarMaxDegreeThreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetPlanarCubic

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET on planar cubic graphs is NP-complete

INSTANCE: a planar graph `G = (V, E)` that is regular of degree `3`, and a positive integer
`K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e., a subset `V' ⊆ V` with
`|V'| ≤ K` such that for all `u ∈ V - V'` there is a `v ∈ V'` for which `{u, v} ∈ E`?

The instance, its graph, the simple-edge-list well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.DominatingSetWanted` ([GT2]). The instance class is that of
`WantedExt.Complexity.NPComplete.DominatingSetPlanarMaxDegreeThreeWanted` (`0 < K ≤ |V|`,
planarity as the repository's `SimpleGraph.IsPlanar`, every degree at most `3`), reused
unchanged, plus Mathlib's `SimpleGraph.IsRegularOfDegree 3`: every vertex has degree exactly
`3`. The degree bound of the reused class is then implied.

Membership in NP: the certificate is `V'`; degrees are checked directly and planarity in linear
time (Hopcroft and Tarjan, J. ACM 21 (1974), 549-568). Hardness: Johnson records the result,
proved by Garey and Johnson (unpublished) and independently by Kikuno and Kakuda (manuscript);
the original proofs were not available.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- Well-formedness of an instance: a well-formed instance of DOMINATING SET on planar graphs of
maximum degree `3` (so `0 < K ≤ |V|` and the graph is planar) whose graph is regular of
degree `3`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSetPlanarMaxDegreeThree.WellFormed i ∧ (Graph i).IsRegularOfDegree 3

open Classical in
/-- DOMINATING SET on planar cubic graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetPlanarCubicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET on planar cubic graphs is NP-complete.** Source: Johnson (1984),
DOMINATING SET [GT2] (Garey and Johnson, unpublished; Kikuno and Kakuda, manuscript). -/
public theorem_wanted dominatingSetPlanarCubic_npComplete :
    dominatingSetPlanarCubicDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetPlanarCubicDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetPlanarCubic
