/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on monopolar graphs: definitions

Source:
M. Barbato and D. Bezzi, "Monopolar graphs: Complexity of computing classical graph
parameters", Discrete Applied Mathematics 291 (2021), 277-285, doi:10.1016/j.dam.2020.12.023;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES;
ISGCI (https://www.graphclasses.org/classes/gc_1272.html), problem "Clique cover" on monopolar
graphs: NP-complete, with the attribution to Barbato and Bezzi.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ClusterDeletionDefs
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesMonopolar

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph WellFormed
  PartitionIntoCliquesFeasible)

/-- A graph is monopolar: its vertex set splits into a stable set `A` and its complement `B`
such that every connected component of `G[B]` is complete. -/
def IsMonopolar {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ A : Set V, G.IsIndepSet A ∧ ClusterDeletion.IsClusterGraph (G.induce Aᶜ)

/-- Well-formedness of an instance: a well-formed PARTITION INTO CLIQUES instance whose graph is
monopolar. -/
def MonopolarWellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  WellFormed i ∧ IsMonopolar (Graph i)

open Classical in
/-- PARTITION INTO CLIQUES on monopolar graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesMonopolarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := PartitionIntoCliquesInstance) x with
  | some i => decide (MonopolarWellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesMonopolar
