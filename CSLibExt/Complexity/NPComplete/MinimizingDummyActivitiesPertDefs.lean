/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMIZING DUMMY ACTIVITIES IN PERT NETWORKS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND44] MINIMIZING DUMMY ACTIVITIES IN
PERT NETWORKS, p. 218;
M. S. Krishnamoorthy and N. Deo, "Complexity of the minimum-dummy-activities problem in a PERT
network", Networks 9 (1979), 189-194, doi:10.1002/net.3230090302.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimizingDummyActivitiesPert

/-- An instance: the number `n` of tasks (vertices `Fin n`), the arc list of `G`, and the bound
`K`. -/
abbrev MinimizingDummyActivitiesInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The precedence graph `G`: an arc `u → v` for each entry `(u, v)` of the arc list. -/
def Graph (i : MinimizingDummyActivitiesInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the arc list has no repeated arcs and its endpoints are
vertices, `G` is acyclic (no vertex has a nonempty path to itself), and `0 < K ≤ |V|`. -/
def WellFormed (i : MinimizingDummyActivitiesInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1) ∧
    (∀ v, ¬ Relation.TransGen (Graph i).Adj v v) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- There is a PERT network with at most `K` dummy activities: events `Fin m`, each the start
`tail i` or the end `head i` of some task, an arc set `A'` that contains the distinct task arcs
`(tail i, head i)`, has at most `|V| + K` arcs, is acyclic, and has a (possibly empty) path from
`head u` to `tail v` exactly when `G` has a nonempty path from `u` to `v`. -/
def MinimizingDummyActivitiesFeasible (i : MinimizingDummyActivitiesInstance) : Prop :=
  ∃ m, ∃ tail head : Fin i.1 → Fin m, ∃ A' : Finset (Fin m × Fin m),
    (∀ e, ∃ v, tail v = e ∨ head v = e) ∧ (∀ v, (tail v, head v) ∈ A') ∧
      Function.Injective (fun v => (tail v, head v)) ∧ A'.card ≤ i.1 + i.2.2 ∧
      (∀ x, ¬ Relation.TransGen (fun a b => (a, b) ∈ A') x x) ∧
      ∀ u v, Relation.ReflTransGen (fun a b => (a, b) ∈ A') (head u) (tail v) ↔
        Relation.TransGen (Graph i).Adj u v

open Classical in
/-- MINIMIZING DUMMY ACTIVITIES IN PERT NETWORKS as a decision problem over bitstrings. -/
noncomputable def minimizingDummyActivitiesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimizingDummyActivitiesInstance) x with
  | some i => decide (WellFormed i ∧ MinimizingDummyActivitiesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimizingDummyActivitiesPert
