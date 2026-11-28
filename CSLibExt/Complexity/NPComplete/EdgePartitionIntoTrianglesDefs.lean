/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE PARTITION INTO TRIANGLES: definitions

Source:
I. Holyer, "The NP-completeness of some edge-partition problems", SIAM Journal on Computing
10(4) (1981), 713-717, doi:10.1137/0210054 (for each fixed `n ≥ 3` it is NP-complete to
determine whether an arbitrary graph can be edge-partitioned into subgraphs isomorphic to the
complete graph `K_n`; here `n = 3`).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgePartitionIntoTriangles

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev EdgePartitionIntoTrianglesInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : EdgePartitionIntoTrianglesInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: a simple edge list on `Fin n` (no repeated edge, no loop,
no reversed copy), so that `i.2.length = |E|`. -/
def WellFormed (i : EdgePartitionIntoTrianglesInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- Some set `T` of triangles of the graph covers every edge exactly once: each member of `T`
is a 3-clique, and every edge `uv` has exactly one member of `T` containing both `u` and
`v`. -/
def EdgePartitionIntoTrianglesFeasible (i : EdgePartitionIntoTrianglesInstance) : Prop :=
  ∃ T : Finset (Finset (Fin i.1)), (∀ t ∈ T, (Graph i).IsNClique 3 t) ∧
    ∀ u v, (Graph i).Adj u v → ∃! t, t ∈ T ∧ u ∈ t ∧ v ∈ t

open Classical in
/-- EDGE PARTITION INTO TRIANGLES as a decision problem over bitstrings. -/
noncomputable def edgePartitionIntoTrianglesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgePartitionIntoTrianglesInstance) x with
  | some i => decide (WellFormed i ∧ EdgePartitionIntoTrianglesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EdgePartitionIntoTriangles
