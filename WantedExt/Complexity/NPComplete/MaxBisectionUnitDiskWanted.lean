/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM BISECTION on unit disk graphs is NP-complete

Source:
J. Díaz and M. Kamiński, "MAX-CUT and MAX-BISECTION are NP-hard on unit disk graphs",
Theoretical Computer Science 377 (2007), 271-276, doi:10.1016/j.tcs.2007.02.013 (preprint
arXiv:cs/0609128), Corollary 11;
ISGCI, class "unit disk" (gc_389), problem Maximum bisection, NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaxBisectionUnitDiskDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxBisectionUnitDisk

open MetaMathlibExt.Complexity.NPComplete.MaxCutUnitDiskGraphs
  (MaxCutUnitDiskGraphsInstance toMaxCut)

/-!
# MAXIMUM BISECTION on unit disk graphs is NP-complete

INSTANCE: a unit disk graph `G = (V, E)`, given with an intersection model, and a positive
integer `K`.
QUESTION: is there a partition of `V` into sets `A`, `B` with `|A| = |B|` (or `|A| = |B| - 1`
when `|V|` is odd) such that at least `K` edges join `A` and `B`?

Díaz and Kamiński prove MAX-BISECTION NP-hard on unit disk graphs (Corollary 11: two disjoint
copies of a unit disk graph form a unit disk graph whose maximum bisection is twice its maximum
cut); a bisection is a partition into two parts of the same cardinality. The ISGCI formulation
used here also admits odd `|V|`, with parts of sizes `⌊|V| / 2⌋` and `⌈|V| / 2⌉`.

The instance and its well-formedness are those of MAX CUT on unit disk graphs
(`WantedExt.Complexity.NPComplete.MaxCutUnitDiskGraphsWanted`, the same paper), reused
unchanged: distinct disk centers with rational coordinates, the edge list of the graph, which
must be exactly the unit disk graph of the centers, and `0 < K`. The question is the bisection
question `MaxBisectionPlanar.MaxBisectionFeasible`
(`WantedExt.Complexity.NPComplete.MaxBisectionPlanarWanted`) on the MAXIMUM CUT instance
`(|P|, E, K)` of the graph.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM BISECTION on unit disk graphs is NP-complete.** Source: Díaz and Kamiński (2007),
Corollary 11; ISGCI (gc_389). -/
public theorem_wanted maxBisectionUnitDisk_npComplete :
    maxBisectionUnitDiskDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxBisectionUnitDiskDec

end MetaMathlibExt.Complexity.NPComplete.MaxBisectionUnitDisk
