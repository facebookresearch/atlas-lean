/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on line graphs of triangle-free graphs: definitions

Source:
A. Munaro, "Bounded clique cover of some sparse graphs", Discrete Mathematics 340(9) (2017),
2208-2216, doi:10.1016/j.disc.2017.04.004;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES and problem [GT1]
VERTEX COVER;
ISGCI (https://www.graphclasses.org/classes/gc_708.html), problem "Clique cover" on line graphs of
triangle-free graphs: NP-complete, with the attribution to Munaro (2017).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesLineGraphTriangleFree

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph WellFormed
  PartitionIntoCliquesFeasible)

/-- `G` is the line graph of a triangle-free graph: `G ≅ L(H)` for a graph `H` on `Fin k`
without a triangle. -/
def IsLineGraphOfTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (H : SimpleGraph (Fin k)), H.CliqueFree 3 ∧ Nonempty (G ≃g H.lineGraph)

/-- Well-formedness of an instance: a well-formed PARTITION INTO CLIQUES instance whose graph is
the line graph of a triangle-free graph. -/
def LineGraphWellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  WellFormed i ∧ IsLineGraphOfTriangleFree (Graph i)

open Classical in
/-- PARTITION INTO CLIQUES on line graphs of triangle-free graphs as a decision problem over
bitstrings. -/
noncomputable def partitionIntoCliquesLineGraphTriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := PartitionIntoCliquesInstance) x with
  | some i => decide (LineGraphWellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesLineGraphTriangleFree
