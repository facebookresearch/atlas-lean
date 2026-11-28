/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH: definitions

Source:
S. Arnborg, D. G. Corneil and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024;
H. L. Bodlaender, É. Bonnet, L. Jaffke, D. Knop, P. T. Lima, M. Milanič, S. Ordyniak, S. Pandey
and O. Suchý, "Treewidth is NP-complete on cubic graphs (and related results)", arXiv:2301.10031
(Section 2: the definitions of tree decompositions, width and treewidth used below, the decision
problem TREEWIDTH, and the attribution of its NP-completeness to Arnborg, Corneil and
Proskurowski; journal version: Electronic Journal of Combinatorics 32(3) (2025), #P3.36,
doi:10.37236/13205).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Treewidth

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, bound `K`. -/
abbrev TreewidthInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TreewidthInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : TreewidthInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- `(T, β)` is a tree decomposition of the finite graph `G`: `T` is a tree, every vertex of `G`
belongs to some bag, for every edge of `G` some bag contains both endpoints, and for every vertex
`v` of `G` the nodes whose bags contain `v` induce a connected subgraph of `T`. -/
def IsTreeDecomposition {V : Type*} [Finite V] (G : SimpleGraph V) {N : ℕ} (T : SimpleGraph (Fin N))
    (β : Fin N → Finset V) : Prop :=
  T.IsTree ∧ (∀ v, ∃ x, v ∈ β x) ∧ (∀ u v, G.Adj u v → ∃ x, u ∈ β x ∧ v ∈ β x) ∧
    ∀ v, (T.induce {x | v ∈ β x}).Connected

/-- The finite graph `G` has treewidth at most `K`: some tree decomposition of `G` has width at
most `K`, i.e. all its bags have at most `K + 1` vertices. -/
def TreewidthAtMost {V : Type*} [Finite V] (G : SimpleGraph V) (K : ℕ) : Prop :=
  ∃ (N : ℕ) (T : SimpleGraph (Fin N)) (β : Fin N → Finset V),
    IsTreeDecomposition G T β ∧ ∀ x, (β x).card ≤ K + 1

/-- The graph of the instance has treewidth at most `K`. -/
def TreewidthFeasible (i : TreewidthInstance) : Prop :=
  TreewidthAtMost (Graph i) i.2.2

open Classical in
/-- TREEWIDTH as a decision problem over bitstrings. -/
noncomputable def treewidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (WellFormed i ∧ TreewidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Treewidth
