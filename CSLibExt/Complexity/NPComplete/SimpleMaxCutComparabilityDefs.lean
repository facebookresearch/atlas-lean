/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on comparability graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND16] MAX CUT, comment ("Remains
NP-complete if `w(e) = 1` for all `e ∈ E` (the SIMPLE MAX CUT problem)"), the problem restricted
here;
R. V. Pocai, "The complexity of SIMPLE MAX-CUT on comparability graphs", Electronic Notes in
Discrete Mathematics 55 (2016), 161-164, doi:10.1016/j.endm.2016.10.040, Theorem 2.3;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ComparabilityGraphSandwichDefs
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutComparability

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

/-- An instance: the vertex count `n`, the edge list, and the bound `K`; this is the MAXIMUM
CUT instance type. -/
abbrev SimpleMaxCutComparabilityInstance := MaxCutInstance

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is a comparability graph, and `0 < K`. -/
def WellFormed (i : SimpleMaxCutComparabilityInstance) : Prop :=
  MaxCut.WellFormed i ∧
    ComparabilityGraphSandwich.IsComparabilityGraph (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧
    0 < i.2.2

/-- A partition `V₁ = S`, `V₂ = V - S` with at least `K` edges between the two sets (the
MAXIMUM CUT question). -/
def SimpleMaxCutComparabilityFeasible (i : SimpleMaxCutComparabilityInstance) : Prop :=
  MaxCutFeasible i

open Classical in
/-- SIMPLE MAX CUT on comparability graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutComparabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SimpleMaxCutComparabilityInstance) x with
  | some i => decide (WellFormed i ∧ SimpleMaxCutComparabilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutComparability
