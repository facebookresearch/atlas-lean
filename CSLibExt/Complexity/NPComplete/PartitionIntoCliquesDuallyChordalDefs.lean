/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on dually chordal graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES (the
parent problem);
A. Brandstädt, F. F. Dragan, V. D. Chepoi and V. I. Voloshin, "Dually chordal graphs", SIAM
Journal on Discrete Mathematics 11(3) (1998), 437-455, doi:10.1137/S0895480193253415 (the
class);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_185` (dually
chordal), problem Clique cover: NP-complete (ISGCI reference note 1504: adding a universal
vertex to any graph gives a dually chordal graph with the same clique cover number).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.IndependentSetDuallyChordalDefs
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesDuallyChordal

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)
open IndependentSetDuallyChordal (DuallyChordal)

/-- Well-formedness of an instance: a well-formed PARTITION INTO CLIQUES instance (a simple edge
list on the vertices `0, ..., n - 1` and `0 < K ≤ n`) whose graph is dually chordal. -/
def WellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ DuallyChordal (Graph i)

open Classical in
/-- PARTITION INTO CLIQUES on dually chordal graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesDuallyChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesDuallyChordal
