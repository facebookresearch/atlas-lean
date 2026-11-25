/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO 4-CYCLES on planar graphs is NP-complete

Source:
F. Berman, D. Johnson, T. Leighton, P. W. Shor and L. Snyder, "Generalized planar matching",
Journal of Algorithms 11 (1990), 153-184, doi:10.1016/0196-6774(90)90001-U;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4 (PARTITION INTO 4-CYCLES).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import WantedExt.Complexity.NPComplete.PartitionIntoIsomorphicSubgraphsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoFourCyclesPlanar

/-!
# PARTITION INTO 4-CYCLES on planar graphs is NP-complete

An instance is a planar graph `G = (V, E)` with `|V| = 4q`. The question is whether `V` can be
partitioned into `q` sets of four vertices, each of which contains a 4-cycle (a spanning copy
of `C₄`, not necessarily induced). This is perfect planar `H`-matching for `H = C₄`.

Berman, Johnson, Leighton, Shor and Snyder (1990) show that "perfect planar `H`-matching is
NP-complete for any connected outerplanar graph `H` with three or more nodes"; `C₄` is such a
graph. Johnson's column (1985) lists PARTITION INTO 4-CYCLES as NP-complete for planar graphs
(and for bipartite graphs) but trivially polynomial for grid graphs. NP membership: every
vertex of a yes-instance lies on a 4-cycle of its part, so `|V| ≤ |E|`; a verifier rejects
larger vertex counts and otherwise checks a partition, so the binary vertex count is harmless.

The statement reuses PARTITION INTO ISOMORPHIC SUBGRAPHS [GT12]
(`PartitionIntoIsomorphicSubgraphsWanted`): its instances carry the pattern graph `H`, which is
fixed here to the 4-cycle `0 - 1 - 2 - 3 - 0`, and its question (every part receives a
bijective homomorphism from `H`, i.e. contains a spanning copy of `H`) is used unchanged.
Planarity is `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, equivalent to
planarity for finite simple graphs by Fáry's theorem).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MetaMathlibExt.Complexity.NPComplete.PartitionIntoIsomorphicSubgraphs
  (PartitionIntoIsomorphicSubgraphsInstance Graph PartitionIntoIsomorphicSubgraphsFeasible)

/-- Well-formedness of an instance: a well-formed PARTITION INTO ISOMORPHIC SUBGRAPHS instance
(simple graphs, `|V|` a positive multiple of `|V_H|`) whose pattern is the 4-cycle
`0 - 1 - 2 - 3 - 0` and whose graph is planar. -/
def WellFormed (i : PartitionIntoIsomorphicSubgraphsInstance) : Prop :=
  PartitionIntoIsomorphicSubgraphs.WellFormed i ∧
    i.2.2 = (4, [(0, 1), (1, 2), (2, 3), (3, 0)]) ∧ (Graph i).IsPlanar

open Classical in
/-- PARTITION INTO 4-CYCLES on planar graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoFourCyclesPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoIsomorphicSubgraphsInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoIsomorphicSubgraphsFeasible i)
  | none => false

/-- **PARTITION INTO 4-CYCLES on planar graphs is NP-complete.** Source: Berman, Johnson,
Leighton, Shor and Snyder (1990); Johnson (1985). -/
public theorem_wanted partitionIntoFourCyclesPlanar_npComplete :
    partitionIntoFourCyclesPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoFourCyclesPlanarDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoFourCyclesPlanar
