/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on planar cubic graphs: definitions

Source:
M. R. Cerioli, L. Faria, T. O. Ferreira, C. A. J. Martinhon, F. Protti and B. Reed,
"Partition into cliques for cubic graphs: Planar case, complexity and approximation", Discrete
Applied Mathematics 156(12) (2008), 2270-2278, doi:10.1016/j.dam.2007.10.015;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesCubicPlanar

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)

open Classical in
/-- Well-formedness of an instance: well formed for PARTITION INTO CLIQUES (a simple graph on
`Fin n` and `0 < K ≤ n`), and the graph is planar and cubic. -/
def WellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ (Graph i).IsPlanar ∧ (Graph i).IsRegularOfDegree 3

open Classical in
/-- PARTITION INTO CLIQUES on planar cubic graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesCubicPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesCubicPlanar
