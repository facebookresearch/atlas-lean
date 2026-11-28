/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAX CUT on unit disk graphs is NP-complete

Source:
J. Díaz and M. Kamiński, "MAX-CUT and MAX-BISECTION are NP-hard on unit disk graphs",
Theoretical Computer Science 377 (2007), 271-276, doi:10.1016/j.tcs.2007.02.013 (preprint
arXiv:cs/0609128).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaxCutUnitDiskGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxCutUnitDiskGraphs

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutFeasible)
open MetaMathlibExt.Complexity.NPComplete.PlanarKMeans (RatCode)
open MetaMathlibExt.Complexity.NPComplete.UnitDiskDominatingSet (unitDiskGraph)

/-!
# MAX CUT on unit disk graphs is NP-complete

INSTANCE: a unit disk graph `G` given with an intersection model, i.e. distinct points of the
plane (the centers of disks of diameter one) such that two vertices are adjacent exactly when
their disks intersect, which happens exactly when the centers are at distance at most `1`; and
a positive integer `K`. QUESTION: is there a partition of the vertices into two sets with at
least `K` edges between them? Díaz and Kamiński prove MAX-CUT NP-hard on unit disk graphs;
membership in NP is immediate (the partition is the certificate).

Points have rational coordinates in the encoding of `PlanarKMeansWanted` (`RatCode`), and the
graph of the model is the repository's `UnitDiskDominatingSet.unitDiskGraph` (distinct points at
Euclidean distance at most `1` are adjacent). The instance lists the points, the edges of `G`,
and `K`: well-formedness requires positive denominators, distinct centers ("the centers of disks
do not coincide"), a MAXIMUM CUT edge list on the vertices `0, ..., |P| - 1`, and that this edge
list is exactly the unit disk graph of the points. The question is MAXIMUM CUT's
(`CSLibExt.Complexity.NPComplete.MaxCutDefs`) on `(|P|, E, K)`, reused unchanged.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAX CUT on unit disk graphs is NP-complete.** Source: Díaz and Kamiński (2007). -/
public theorem_wanted maxCutUnitDiskGraphs_npComplete :
    maxCutUnitDiskGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxCutUnitDiskGraphsDec

end MetaMathlibExt.Complexity.NPComplete.MaxCutUnitDiskGraphs
