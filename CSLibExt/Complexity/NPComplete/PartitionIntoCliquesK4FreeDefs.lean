/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES for K₄-free graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES, comment:
remains NP-complete for graphs containing no complete subgraphs on 4 vertices (see the
construction for PARTITION INTO TRIANGLES in Chapter 3, Theorem 3.7);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (the unrestricted
problem, there called CLIQUE COVER).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesK4Free

open MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliques
  (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)

/-- Well-formedness of an instance: a well-formed PARTITION INTO CLIQUES instance (simple edge
list, `0 < K ≤ |V|`) whose graph contains no complete subgraph on 4 vertices. -/
def WellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ (Graph i).CliqueFree 4

open Classical in
/-- PARTITION INTO CLIQUES for K₄-free graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesK4FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesK4Free
