/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITATED VEHICLE ROUTING ON TREES: definitions

Source:
M. Labbé, G. Laporte and H. Mercure, "Capacitated vehicle routing on trees", Operations
Research 39 (1991), 616-622, doi:10.1287/opre.39.4.616.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedVehicleRoutingTrees

/-- An instance: vertex count `n`, edges as `(u, v, length)`, vertex weights (indexed by
vertex), vehicle capacity `Q`, objective coefficients `α` (per vehicle) and `β` (per unit of
distance), and the bound `B`. -/
abbrev CapacitatedVehicleRoutingTreesInstance :=
  ℕ × List (ℕ × ℕ × ℕ) × List ℕ × ℕ × ℕ × ℕ × ℕ

/-- The endpoint pairs of the edge list. -/
def endpoints (i : CapacitatedVehicleRoutingTreesInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CapacitatedVehicleRoutingTreesInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (endpoints i)

/-- The length of an edge (the length of the first list entry with these endpoints; in a
well-formed instance there is exactly one). -/
def edgeLength (i : CapacitatedVehicleRoutingTreesInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)).map fun e => e.2.2).getD 0

/-- The weight of vertex `v`. -/
def weight (i : CapacitatedVehicleRoutingTreesInstance) (v : Fin i.1) : ℕ :=
  i.2.2.1.getD v 0

/-- Well-formedness of an instance: a simple edge list on `Fin n` (no loops, no repeated or
reversed edges), one weight per vertex, and the graph is a tree. -/
def WellFormed (i : CapacitatedVehicleRoutingTreesInstance) : Prop :=
  ((endpoints i).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧ (e.2.1, e.1) ∉ endpoints i) ∧
    i.2.2.1.length = i.1 ∧ (Graph i).IsTree

/-- There are `m` closed walks `C k` at the depot `v₀ = 0` and an assignment `s` of every
vertex of positive weight to one walk, such that every such vertex lies on its walk, the
weight assigned to each walk is at most `Q`, and `α · m + β · (total walk length) ≤ B`. -/
def CapacitatedVehicleRoutingTreesFeasible (i : CapacitatedVehicleRoutingTreesInstance) :
    Prop :=
  ∃ v₀ : Fin i.1, (v₀ : ℕ) = 0 ∧
    ∃ (m : ℕ) (C : Fin m → (Graph i).Walk v₀ v₀) (s : {v : Fin i.1 // 0 < weight i v} → Fin m),
      (∀ v, v.1 ∈ (C (s v)).support) ∧
      (∀ k, ∑ v ∈ Finset.univ.filter (fun v => s v = k), weight i v.1 ≤ i.2.2.2.1) ∧
      i.2.2.2.2.1 * m + i.2.2.2.2.2.1 * ∑ k, ((C k).edges.map (edgeLength i)).sum ≤
        i.2.2.2.2.2.2

open Classical in
/-- CAPACITATED VEHICLE ROUTING ON TREES as a decision problem over bitstrings. -/
noncomputable def capacitatedVehicleRoutingTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CapacitatedVehicleRoutingTreesInstance) x with
  | some i => decide (WellFormed i ∧ CapacitatedVehicleRoutingTreesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CapacitatedVehicleRoutingTrees
