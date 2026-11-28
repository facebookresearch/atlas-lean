/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX for comparability graphs: definitions

Source:
L. Cai and J. A. Ellis, "NP-completeness of edge-colouring some restricted graphs", Discrete
Applied Mathematics 30(1) (1991), 15-27, doi:10.1016/0166-218X(91)90010-T;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021
(arXiv:2104.14395), Section 2 ("L. Cai and J. A. Ellis proved that deciding whether χ′(G) = 3 is
NP-complete even for COMPARABILITY graphs and for LINE graphs").
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ComparabilityGraphSandwichDefs
public import CSLibExt.Complexity.NPComplete.EdgeColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticIndexComparability

open EdgeColoring (EdgeColoringInstance EdgeColoringFeasible)

/-- Well-formedness of an instance: a well-formed CHROMATIC INDEX instance (a simple edge list on
`Fin n`) whose graph is a comparability graph, and `0 < K`. -/
def WellFormed (i : EdgeColoringInstance) : Prop :=
  EdgeColoring.WellFormed i ∧
    ComparabilityGraphSandwich.IsComparabilityGraph (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧
    0 < i.2.2

open Classical in
/-- CHROMATIC INDEX for comparability graphs as a decision problem
over bitstrings. -/
noncomputable def chromaticIndexComparabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeColoringInstance) x with
  | some i => decide (WellFormed i ∧ EdgeColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChromaticIndexComparability
