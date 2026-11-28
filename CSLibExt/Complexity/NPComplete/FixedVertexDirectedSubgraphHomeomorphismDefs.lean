/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIXED-VERTEX DIRECTED SUBGRAPH HOMEOMORPHISM: definitions

Source:
S. Fortune, J. Hopcroft and J. Wyllie, "The directed subgraph homeomorphism problem",
Theoretical Computer Science 10 (1980), 111-121, doi:10.1016/0304-3975(80)90009-2;
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 2 (1981), 393-405,
doi:10.1016/0196-6774(81)90037-7, entry [2] SUBGRAPH HOMEOMORPHISM (FOR A FIXED GRAPH H).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FixedVertexDirectedSubgraphHomeomorphism

open MetaMathlibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPaths (IsDirectedPath)

/-- The fixed pattern `H`: `k` vertices `0, ..., k - 1` and the arc list `A_H` has no repeated
arcs, no loops, and endpoints among the vertices. -/
def PatternWellFormed (k : ℕ) (AH : List (ℕ × ℕ)) : Prop :=
  AH.Nodup ∧ ∀ a ∈ AH, a.1 < k ∧ a.2 < k ∧ a.1 ≠ a.2

/-- An instance: vertex count `n` of `G` (vertices `0, ..., n - 1`), arc list of `G`, and the
prescribed images `[m 0, ..., m (k - 1)]` of the pattern vertices. -/
abbrev FixedVertexDirectedSubgraphHomeomorphismInstance := ℕ × List (ℕ × ℕ) × List ℕ

/-- Well-formedness of an instance for a pattern with `k` vertices: the arcs of `G` are distinct,
loopless and between vertices, and `m` lists `k` pairwise distinct vertices (`m` is injective). -/
def WellFormed (k : ℕ) (i : FixedVertexDirectedSubgraphHomeomorphismInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
    i.2.2.length = k ∧ i.2.2.Nodup ∧ ∀ v ∈ i.2.2, v < i.1

/-- `G` contains a subdivision of the pattern with arc list `AH` and branch vertices `m`: the
`j`-th path is a directed path from `m u` to `m v` for the `j`-th arc `(u, v)` of `AH`, every
prescribed vertex on it is one of its two ends, and two different paths share only prescribed
vertices. -/
def FixedVertexDirectedSubgraphHomeomorphismFeasible (AH : List (ℕ × ℕ))
    (i : FixedVertexDirectedSubgraphHomeomorphismInstance) : Prop :=
  ∃ paths : List (List ℕ),
    List.Forall₂ (fun a p => IsDirectedPath i.2.1 (i.2.2.getD a.1 0) (i.2.2.getD a.2 0) p ∧
      ∀ x ∈ p, x ∈ i.2.2 → x = i.2.2.getD a.1 0 ∨ x = i.2.2.getD a.2 0) AH paths ∧
    paths.Pairwise fun p q => ∀ x ∈ p, x ∈ q → x ∈ i.2.2

open Classical in
/-- FIXED-VERTEX DIRECTED SUBGRAPH HOMEOMORPHISM for the pattern `(k, AH)`, as a decision problem
over bitstrings. -/
noncomputable def fixedVertexDirectedSubgraphHomeomorphismDec (k : ℕ) (AH : List (ℕ × ℕ)) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FixedVertexDirectedSubgraphHomeomorphismInstance) x with
  | some i => decide (WellFormed k i ∧ FixedVertexDirectedSubgraphHomeomorphismFeasible AH i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FixedVertexDirectedSubgraphHomeomorphism
