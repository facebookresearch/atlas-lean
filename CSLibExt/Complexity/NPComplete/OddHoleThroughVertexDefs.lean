/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ODD HOLE THROUGH A GIVEN VERTEX: definitions

Source:
D. Bienstock, "On the complexity of testing for odd holes and induced odd paths", Discrete
Mathematics 90 (1991), 85-92, doi:10.1016/0012-365X(91)90098-M, and "Corrigendum", Discrete
Mathematics 102 (1992), 109;
M. Chudnovsky, A. Scott, P. Seymour and S. Spirkl, "Detecting an odd hole", Journal of the ACM
67 (2020), Article 5, doi:10.1145/3375720 (arXiv:1903.00208; Section 1: "D. Bienstock [2, 3]
showed that testing if a graph has an odd hole containing a given vertex is NP-complete").
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OddHoleThroughVertex

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, given vertex `v`. -/
abbrev OddHoleThroughVertexInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : OddHoleThroughVertexInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `v < n`. -/
def WellFormed (i : OddHoleThroughVertexInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2 < i.1

/-- The graph has an odd hole through `v`: an induced cycle `cycleGraph k ↪g G` of odd length
`k ≥ 4` (hence `k ≥ 5`) one of whose vertices is mapped to `v`. -/
def OddHoleThroughVertexFeasible (i : OddHoleThroughVertexInstance) : Prop :=
  ∃ k : ℕ, 4 ≤ k ∧ Odd k ∧
    ∃ f : SimpleGraph.cycleGraph k ↪g Graph i, ∃ x, ((f x : Fin i.1) : ℕ) = i.2.2

open Classical in
/-- ODD HOLE THROUGH A GIVEN VERTEX as a decision problem over bitstrings. -/
noncomputable def oddHoleThroughVertexDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OddHoleThroughVertexInstance) x with
  | some i => decide (WellFormed i ∧ OddHoleThroughVertexFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OddHoleThroughVertex
