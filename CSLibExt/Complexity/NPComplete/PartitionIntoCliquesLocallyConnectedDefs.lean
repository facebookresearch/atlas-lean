/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on locally connected graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES (the
parent problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_932` (locally
connected), problem Clique cover: NP-complete, reference `ref_1506` (ISGCI note: adding a
universal vertex to a connected graph yields a locally connected graph with the same clique
cover number; communicated by P. Irzhavski). No published proof was found.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesLocallyConnected

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)

/-- Well-formedness of an instance: a well-formed PARTITION INTO CLIQUES instance (a simple edge
list on `Fin n`, `0 < K ≤ |V|`) whose graph is locally connected (the neighbourhood of every
vertex induces a connected graph). -/
def WellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧
    ∀ v, ((Graph i).induce ((Graph i).neighborSet v)).Connected

open Classical in
/-- PARTITION INTO CLIQUES on locally connected graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesLocallyConnectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesLocallyConnected
