/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIT-LENGTH TREE EMBEDDING IN THE GRID: definitions

Source:
S. N. Bhatt and S. S. Cosmadakis, "The complexity of minimizing wire lengths in VLSI
layouts", Information Processing Letters 25 (1987), 263-267,
doi:10.1016/0020-0190(87)90173-6;
V. G. P. de Sá, G. D. da Fonseca, R. C. S. Machado and C. M. H. de Figueiredo,
"Complexity dichotomy on partial grid recognition", Theoretical Computer Science 412 (2011),
2370-2379, doi:10.1016/j.tcs.2011.01.018.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Copy

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitLengthTreeGridEmbedding

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev UnitLengthTreeGridEmbeddingInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : UnitLengthTreeGridEmbeddingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and that graph is a
tree. -/
def WellFormed (i : UnitLengthTreeGridEmbeddingInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).IsTree

/-- The tree is a subgraph of the infinite square grid: it is contained in
`hypercubicLattice 2`. -/
def UnitLengthTreeGridEmbeddingFeasible (i : UnitLengthTreeGridEmbeddingInstance) : Prop :=
  (Graph i).IsContained (StatMech.Lattice.hypercubicLattice 2)

open Classical in
/-- UNIT-LENGTH TREE EMBEDDING IN THE GRID as a decision problem over bitstrings. -/
noncomputable def unitLengthTreeGridEmbeddingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitLengthTreeGridEmbeddingInstance) x with
  | some i => decide (WellFormed i ∧ UnitLengthTreeGridEmbeddingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitLengthTreeGridEmbedding
