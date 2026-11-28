/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITIONED GRAPH ISOMORPHISM: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide" (fourth edition), Journal of
Algorithms 3 (1982), 288-300, doi:10.1016/0196-6774(82)90026-8, problem [2] PARTITIONED GRAPH
ISOMORPHISM (reference: F. Yao; transformation from EXACT COVER BY 3-SETS);
F. F. Yao, "Graph 2-isomorphism is NP-complete", Information Processing Letters 9 (1979),
68-72, doi:10.1016/0020-0190(79)90130-3.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionedGraphIsomorphism

/-- An instance: vertex count `n` and edge list of `G`, vertex count `m` and edge list of `H`,
and the number of parts `K`. -/
abbrev PartitionedGraphIsomorphismInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ) × ℕ

/-- The graph `G` of the instance as a `SimpleGraph (Fin n)`. -/
def GraphG (i : PartitionedGraphIsomorphismInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The graph `H` of the instance as a `SimpleGraph (Fin m)`. -/
def GraphH (i : PartitionedGraphIsomorphismInstance) : SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2.1

/-- Well-formedness of an instance: both edge lists are simple (no repeats, no self-loops, no
reversed duplicates, endpoints below the vertex count), and `K` is positive. -/
def WellFormed (i : PartitionedGraphIsomorphismInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (i.2.2.2.1.Nodup ∧ ∀ e ∈ i.2.2.2.1,
      e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2.1) ∧
    0 < i.2.2.2.2

/-- The edge sets of `G` and `H` split into `K` pairwise disjoint, possibly empty parts
`Gs k` and `Hs k` with `Gs k ≃g Hs k` for every part `k`. -/
def PartitionedGraphIsomorphismFeasible (i : PartitionedGraphIsomorphismInstance) : Prop :=
  ∃ (Gs : Fin i.2.2.2.2 → SimpleGraph (Fin i.1)) (Hs : Fin i.2.2.2.2 → SimpleGraph (Fin i.2.2.1)),
    (Pairwise fun k l => Disjoint (Gs k) (Gs l)) ∧ (⨆ k, Gs k) = GraphG i ∧
      (Pairwise fun k l => Disjoint (Hs k) (Hs l)) ∧ (⨆ k, Hs k) = GraphH i ∧
        ∀ k, Nonempty (Gs k ≃g Hs k)

open Classical in
/-- PARTITIONED GRAPH ISOMORPHISM as a decision problem over bitstrings. -/
noncomputable def partitionedGraphIsomorphismDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionedGraphIsomorphismInstance) x with
  | some i => decide (WellFormed i ∧ PartitionedGraphIsomorphismFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionedGraphIsomorphism
