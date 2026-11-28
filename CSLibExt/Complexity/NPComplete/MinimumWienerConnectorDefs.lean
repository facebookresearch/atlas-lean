/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM WIENER CONNECTOR: definitions

Source:
N. Ruchansky, F. Bonchi, D. García-Soriano, F. Gullo and N. Kourtellis, "The minimum Wiener
connector problem", in *Proceedings of the 2015 ACM SIGMOD International Conference on
Management of Data* (2015), 1587-1602, doi:10.1145/2723372.2749449 (Problem 1 and Theorem 2;
arXiv:1504.00513).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumWienerConnector

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list, the query vertices `Q`, and
the bound `K`. -/
abbrev MinimumWienerConnectorInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MinimumWienerConnectorInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The Wiener index of the subgraph of `G` induced by `S`: the sum, over the unordered pairs
`{u, v} ⊆ S` (listed as `u < v`), of the distance between `u` and `v` in `G.induce S`. -/
noncomputable def wienerIndex {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  ∑ u ∈ S.attach, ∑ v ∈ S.attach,
    if u.1 < v.1 then
      (G.induce (S : Set (Fin n))).dist ⟨u.1, Finset.mem_coe.2 u.2⟩ ⟨v.1, Finset.mem_coe.2 v.2⟩
    else 0

/-- Well-formedness of an instance: the edge list is a simple undirected edge list on `Fin n`,
the graph is connected, the query vertices are distinct vertices, and `0 < K`. -/
def WellFormed (i : MinimumWienerConnectorInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).Connected ∧ i.2.2.1.Nodup ∧ (∀ q ∈ i.2.2.1, q < i.1) ∧ 0 < i.2.2.2

/-- Some vertex set `S` containing every query vertex induces a connected subgraph of Wiener
index at most `K`. -/
def MinimumWienerConnectorFeasible (i : MinimumWienerConnectorInstance) : Prop :=
  ∃ S : Finset (Fin i.1), (∀ q ∈ i.2.2.1, ∃ v ∈ S, (v : ℕ) = q) ∧
    ((Graph i).induce (S : Set (Fin i.1))).Connected ∧ wienerIndex (Graph i) S ≤ i.2.2.2

open Classical in
/-- MINIMUM WIENER CONNECTOR as a decision problem over bitstrings. -/
noncomputable def minimumWienerConnectorDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumWienerConnectorInstance) x with
  | some i => decide (WellFormed i ∧ MinimumWienerConnectorFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumWienerConnector
