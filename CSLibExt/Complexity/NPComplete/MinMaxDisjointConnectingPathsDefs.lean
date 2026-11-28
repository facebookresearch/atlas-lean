/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM MAXIMUM DISJOINT CONNECTING PATHS: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM MAXIMUM DISJOINT CONNECTING PATHS (decision version);
C.-L. Li, S. T. McCormick and D. Simchi-Levi, "The complexity of finding two disjoint paths
with min-max objective function", Discrete Appl. Math. 26 (1990), 105-115,
doi:10.1016/0166-218X(90)90024-7.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.Graph.MengerVertex
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinMaxDisjointConnectingPaths



open MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), edge list with lengths
`(u, v, l(u, v))`, `s`, `t`, and `K`. -/
abbrev MinMaxDisjointConnectingPathsInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MinMaxDisjointConnectingPathsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1.map fun e => (e.1, e.2.1))

/-- The length of an edge `e`: the length recorded for the list entry whose endpoints are the
endpoints of `e` (unique under `WellFormed`). -/
def edgeLength (i : MinMaxDisjointConnectingPathsInstance) (e : Sym2 (Fin i.1)) : ℕ :=
  ((i.2.1.find? fun d => e.map Fin.val = s(d.1, d.2.1)).map fun d => d.2.2).getD 0

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `s` and `t` are
distinct vertices, and `K` is positive. -/
def WellFormed (i : MinMaxDisjointConnectingPathsInstance) : Prop :=
  ((i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ i.2.2.1 ≠ i.2.2.2.1 ∧ 0 < i.2.2.2.2

/-- There are two different paths from `s` to `t` in `G` sharing no vertex other than `s` and
`t`, each of total length at most `K`. -/
def MinMaxDisjointConnectingPathsFeasible (i : MinMaxDisjointConnectingPathsInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1)
    (paths : Fin 2 → (Graph i).Path ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩),
    Function.Injective paths ∧ IsInternallyVertexDisjointSTPaths paths ∧
      ∀ j, ((paths j).val.edges.map (edgeLength i)).sum ≤ i.2.2.2.2

open Classical in
/-- MINIMUM MAXIMUM DISJOINT CONNECTING PATHS as a decision problem over bitstrings. -/
noncomputable def minMaxDisjointConnectingPathsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinMaxDisjointConnectingPathsInstance) x with
  | some i => decide (WellFormed i ∧ MinMaxDisjointConnectingPathsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinMaxDisjointConnectingPaths
