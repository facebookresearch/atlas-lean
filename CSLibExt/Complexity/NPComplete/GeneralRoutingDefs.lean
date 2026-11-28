/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERAL ROUTING: definitions

Source:
J. K. Lenstra and A. H. G. Rinnooy Kan, "On general routing problems", Networks 6 (1976),
273-280, doi:10.1002/net.3230060305 (Section 2: the general routing problem, and the theorem
that its special case `Q = ∅`, the rural postman problem, is polynomial complete);
C. S. Orloff, "A fundamental problem in vehicle routing", Networks 4 (1974), 35-64,
doi:10.1002/net.3230040105 (definition of the problem);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM GENERAL ROUTING ("Generalization of ND27" of Garey and Johnson (1979)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.RuralPostmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralRouting

open MetaMathlibExt.Complexity.NPComplete.RuralPostman (RuralPostmanInstance)

/-- An instance: a `RuralPostman` instance `(n, edges with lengths, E', B)` and the list of
required vertices `V'`. -/
abbrev GeneralRoutingInstance := RuralPostmanInstance × List ℕ

/-- Well-formedness of an instance: the parent's conditions (simple edge list on `Fin n`,
required edges in the graph, `0 < B`), and every required vertex is a vertex. -/
def WellFormed (i : GeneralRoutingInstance) : Prop :=
  RuralPostman.WellFormed i.1 ∧ ∀ q ∈ i.2, q < i.1.1

/-- Some closed walk visits every required vertex, traverses every required edge, and has total
length at most `B` (each traversal of an edge counts its length). -/
def GeneralRoutingFeasible (i : GeneralRoutingInstance) : Prop :=
  ∃ v, ∃ c : (RuralPostman.Graph i.1).Walk v v,
    (∀ q ∈ i.2, q ∈ c.support.map Fin.val) ∧
      (∀ r ∈ i.1.2.2.1, s(r.1, r.2) ∈ c.edges.map (Sym2.map Fin.val)) ∧
        (c.edges.map (RuralPostman.edgeLength i.1)).sum ≤ i.1.2.2.2

open Classical in
/-- GENERAL ROUTING as a decision problem over bitstrings. -/
noncomputable def generalRoutingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeneralRoutingInstance) x with
  | some i => decide (WellFormed i ∧ GeneralRoutingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeneralRouting
