/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PERFECT H-PACKING: definitions

Source:
D. G. Kirkpatrick and P. Hell, "On the completeness of a generalized matching
problem", Proceedings of the 10th Annual ACM Symposium on Theory of Computing
(1978), 240-245, doi:10.1145/800133.804353;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), comment to problem [GT12]
PARTITION INTO ISOMORPHIC SUBGRAPHS.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PartitionIntoIsomorphicSubgraphsDefs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PerfectHPacking

/-- An instance: vertex count `n` of `G` (vertices `Fin n`) and the edge list of `G`. -/
abbrev PerfectHPackingInstance := ℕ × List (ℕ × ℕ)

/-- The PARTITION INTO ISOMORPHIC SUBGRAPHS instance with graph `G = i` and pattern
`H = (m, hs)`. -/
def withPattern (m : ℕ) (hs : List (ℕ × ℕ)) (i : PerfectHPackingInstance) :
    PartitionIntoIsomorphicSubgraphs.PartitionIntoIsomorphicSubgraphsInstance :=
  (i.1, i.2, m, hs)

/-- A pattern `H = (m, hs)` for which the theorem is stated: `hs` is a simple edge list on
`Fin m` (no duplicate edges in either orientation, no self-loops, endpoints in range), and `H`
has a connected component with at least 3 vertices. -/
def ValidPattern (m : ℕ) (hs : List (ℕ × ℕ)) : Prop :=
  (hs.Nodup ∧ ∀ e ∈ hs, e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ hs) ∧
    ∃ c : (Cslib.Complexity.Karp.edgeGraph m hs).ConnectedComponent, 3 ≤ c.supp.ncard

open Classical in
/-- PERFECT H-PACKING for the fixed pattern `H = (m, hs)` as a decision problem over
bitstrings. -/
noncomputable def perfectHPackingDec (m : ℕ) (hs : List (ℕ × ℕ)) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := PerfectHPackingInstance) x with
  | some i => decide (PartitionIntoIsomorphicSubgraphs.WellFormed (withPattern m hs i) ∧
      PartitionIntoIsomorphicSubgraphs.PartitionIntoIsomorphicSubgraphsFeasible
        (withPattern m hs i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PerfectHPacking
