/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE EMBEDDING ON A GRID is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND47] EDGE EMBEDDING ON A GRID, p. 219,
crediting F. Gavril, "Some NP-complete problems on graphs", Proceedings of the 11th Conference on
Information Sciences and Systems, Johns Hopkins University, Baltimore (1977), 91-95
(transformation from 3-PARTITION).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import MathlibExt.Combinatorics.SimpleGraph.RookGraph

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeEmbeddingOnAGrid

/-!
# EDGE EMBEDDING ON A GRID is NP-complete

INSTANCE: a graph `G = (V, E)` and positive integers `M`, `N`.
QUESTION: is there a one-to-one function `f : V → {1, 2, …, M} × {1, 2, …, N}` such that if
`{u, v} ∈ E`, `f(u) = (x₁, y₁)` and `f(v) = (x₂, y₂)`, then either `x₁ = x₂` or `y₁ = y₂`, i.e.
`f(u)` and `f(v)` are both on the same "line" of the grid?

Grid coordinates are `0`-based (`Fin M × Fin N`, a relabelling of `{1, …, M} × {1, …, N}`).
Two distinct grid points on a common line are exactly the adjacent vertices of MathlibExt's rook
graph `SimpleGraph.rookGraph M N`, so a one-to-one `f` sending edges to pairs on a common line
is an injective graph homomorphism `G →g rookGraph M N`, i.e. `G` is contained in the rook graph
(Mathlib's `SimpleGraph.IsContained`, a `SimpleGraph.Copy`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, `M`, `N`. -/
abbrev EdgeEmbeddingOnAGridInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : EdgeEmbeddingOnAGridInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `M`, `N` are
positive. -/
def WellFormed (i : EdgeEmbeddingOnAGridInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- A one-to-one placement of the vertices on the `M × N` grid in which the two ends of every
edge share a row or a column: `G` is contained in the rook graph on `Fin M × Fin N`. -/
def EdgeEmbeddingOnAGridFeasible (i : EdgeEmbeddingOnAGridInstance) : Prop :=
  (Graph i).IsContained (SimpleGraph.rookGraph i.2.2.1 i.2.2.2)

open Classical in
/-- EDGE EMBEDDING ON A GRID as a decision problem over bitstrings. -/
noncomputable def edgeEmbeddingOnAGridDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeEmbeddingOnAGridInstance) x with
  | some i => decide (WellFormed i ∧ EdgeEmbeddingOnAGridFeasible i)
  | none => false

/-- **EDGE EMBEDDING ON A GRID is NP-complete.** Source: Garey and Johnson (1979), [ND47];
Gavril (1977). -/
public theorem_wanted edgeEmbeddingOnAGrid_npComplete :
    edgeEmbeddingOnAGridDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgeEmbeddingOnAGridDec

end MetaMathlibExt.Complexity.NPComplete.EdgeEmbeddingOnAGrid
