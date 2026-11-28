/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES for line graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES (comment: "Remains
NP-complete for edge graphs [Arjomandi, 1977]"); D. S. Johnson, "The NP-completeness column: an
ongoing guide" (sixteenth edition), Journal of Algorithms 6 (1985), 434-451,
doi:10.1016/0196-6774(85)90012-4, Table 1 (row "Edge (or Line)", partition into cliques); A.
Munaro, "Bounded clique cover of some sparse graphs", Discrete Mathematics 340 (2017), 2208-2216,
doi:10.1016/j.disc.2017.04.004 (NP-complete already for line graphs of triangle-free graphs, a
subclass).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesLineGraphs

open MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliques
  (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)

/-- Well-formedness of an instance: the parent's (simple edge list, `0 < K ≤ |V|`) and the graph
is a line graph. -/
def WellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ MetaMathlibExt.SimpleGraph.IsLineGraph (Graph i)

open Classical in
/-- PARTITION INTO CLIQUES for line graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesLineGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesLineGraphs
