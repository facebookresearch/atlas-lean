/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO 4-CYCLES on planar graphs: definitions

Source:
F. Berman, D. Johnson, T. Leighton, P. W. Shor and L. Snyder, "Generalized planar matching",
Journal of Algorithms 11 (1990), 153-184, doi:10.1016/0196-6774(90)90001-U;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4 (PARTITION INTO 4-CYCLES).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.PartitionIntoIsomorphicSubgraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoFourCyclesPlanar



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

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoFourCyclesPlanar
