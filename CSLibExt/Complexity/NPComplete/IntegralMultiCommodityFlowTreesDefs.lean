/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGRAL K-MULTICOMMODITY FLOW ON TREES: definitions

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MAXIMUM INTEGRAL K-MULTICOMMODITY FLOW ON TREES;
N. Garg, V. V. Vazirani and M. Yannakakis, "Primal-dual approximation algorithms for integral
flow and multicut in trees", Algorithmica 18 (1997), 3-20, doi:10.1007/BF02523685.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegralMultiCommodityFlowTrees

/-- An instance: vertex count `n` (vertices `Fin n`), the edges `(u, v, c(e))` with their
capacities, the pairs `(sᵢ, tᵢ)`, and the bound `K`. -/
abbrev IntegralMultiCommodityFlowTreesInstance :=
  ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The edge list of the instance, without capacities. -/
def edges (i : IntegralMultiCommodityFlowTreesInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IntegralMultiCommodityFlowTreesInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (edges i)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) that is a tree, every
pair consists of two distinct vertices, and `0 < K`. -/
def WellFormed (i : IntegralMultiCommodityFlowTreesInstance) : Prop :=
  ((edges i).Nodup ∧
      ∀ e ∈ edges i, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ edges i) ∧
    (Graph i).IsTree ∧ (∀ p ∈ i.2.2.1, p.1 < i.1 ∧ p.2 < i.1 ∧ p.1 ≠ p.2) ∧ 0 < i.2.2.2

/-- The edge `{u, v}` belongs to a path from `s` to `t` in the graph of the instance (in a tree,
to the unique such path). -/
def OnPath (i : IntegralMultiCommodityFlowTreesInstance) (s t u v : ℕ) : Prop :=
  ∃ (a b : Fin i.1) (p : (Graph i).Walk a b), (a : ℕ) = s ∧ (b : ℕ) = t ∧ p.IsPath ∧
    s(u, v) ∈ p.edges.map (Sym2.map Fin.val)

open Classical in
/-- Flows `fᵢ ∈ ℕ`, one per pair, within every edge capacity, with total at least `K`. -/
def IntegralMultiCommodityFlowTreesFeasible (i : IntegralMultiCommodityFlowTreesInstance) :
    Prop :=
  ∃ f : Fin i.2.2.1.length → ℕ,
    (∀ e ∈ i.2.1,
      ∑ j, (if OnPath i i.2.2.1[j].1 i.2.2.1[j].2 e.1 e.2.1 then f j else 0) ≤ e.2.2) ∧
    i.2.2.2 ≤ ∑ j, f j

open Classical in
/-- INTEGRAL K-MULTICOMMODITY FLOW ON TREES as a decision problem over bitstrings. -/
noncomputable def integralMultiCommodityFlowTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntegralMultiCommodityFlowTreesInstance) x with
  | some i => decide (WellFormed i ∧ IntegralMultiCommodityFlowTreesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntegralMultiCommodityFlowTrees
