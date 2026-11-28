/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH HOMOMORPHISM onto a triangle: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT52] GRAPH HOMOMORPHISM, p. 203,
comment: "Remains NP-complete for H fixed to be a triangle" (no separate attribution; the entry
cites L. A. Levin, "Universal sequential search problems", Problemy Peredachi Informatsii 9(3)
(1973), 115-116, for the problem with `H` part of the instance).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphHomomorphismIdentificationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphHomomorphismTriangle

open MetaMathlibExt.Complexity.NPComplete.GraphHomomorphismIdentification

/-- An instance: vertex count and edge list of `G`. -/
abbrev GraphHomomorphismTriangleInstance := ℕ × List (ℕ × ℕ)

/-- The GRAPH HOMOMORPHISM instance with graph `G` and `H` the triangle on `Fin 3`. -/
abbrev withTriangle (i : GraphHomomorphismTriangleInstance) :
    GraphHomomorphismIdentificationInstance :=
  (i.1, i.2, 3, [(0, 1), (0, 2), (1, 2)])

open Classical in
/-- GRAPH HOMOMORPHISM onto a triangle as a decision problem over bitstrings. -/
noncomputable def graphHomomorphismTriangleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphHomomorphismTriangleInstance) x with
  | some i => decide (GraphHomomorphismIdentification.WellFormed (withTriangle i) ∧
      GraphHomomorphismIdentificationFeasible (withTriangle i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphHomomorphismTriangle
