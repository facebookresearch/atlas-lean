/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH HOMOMORPHISM (identification of nonadjacent vertices): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT52] GRAPH HOMOMORPHISM;
L. A. Levin, "Universal sequential search problems", Problemy Peredachi Informatsii 9(3)
(1973), 115-116; English translation in Problems of Information Transmission 9 (1973),
265-266.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphHomomorphismIdentification

/-- An instance: vertex count and edge list of `G`, vertex count and edge list of `H`. -/
abbrev GraphHomomorphismIdentificationInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)

/-- The graph `G` as a `SimpleGraph (Fin n₁)`. -/
def GraphG (i : GraphHomomorphismIdentificationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The graph `H` as a `SimpleGraph (Fin n₂)`. -/
def GraphH (i : GraphHomomorphismIdentificationInstance) : SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2

/-- Well-formedness of an instance: both edge lists are simple (in range, no loops, no
repeated edge in either orientation). -/
def WellFormed (i : GraphHomomorphismIdentificationInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.2.Nodup ∧
      ∀ e ∈ i.2.2.2, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2

/-- `H` is obtained from `G` by identifying nonadjacent vertices: some surjective map
`f : V₁ → V₂` has fibers that are independent sets of `G`, and the quotient of `G` by its
fibers is `H`. -/
def GraphHomomorphismIdentificationFeasible (i : GraphHomomorphismIdentificationInstance) :
    Prop :=
  ∃ f : Fin i.1 → Fin i.2.2.1, Function.Surjective f ∧
    (∀ x, (GraphG i).IsIndepSet {v | f v = x}) ∧ (GraphG i).map f = GraphH i

open Classical in
/-- GRAPH HOMOMORPHISM ([GT52]) as a decision problem over bitstrings. -/
noncomputable def graphHomomorphismIdentificationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphHomomorphismIdentificationInstance) x with
  | some i => decide (WellFormed i ∧ GraphHomomorphismIdentificationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphHomomorphismIdentification
