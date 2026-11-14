/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PERFECT H-PACKING is NP-complete for every fixed H with a component of at least 3 vertices

Source:
D. G. Kirkpatrick and P. Hell, "On the completeness of a generalized matching
problem", Proceedings of the 10th Annual ACM Symposium on Theory of Computing
(1978), 240-245, doi:10.1145/800133.804353;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), comment to problem [GT12]
PARTITION INTO ISOMORPHIC SUBGRAPHS.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PartitionIntoIsomorphicSubgraphsWanted
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PerfectHPacking

/-!
# PERFECT H-PACKING is NP-complete for every fixed H with a component of at least 3 vertices

For a fixed graph `H`: INSTANCE: a graph `G = (V, E)` with `|V|` divisible by `|V(H)|`.
QUESTION: can `V` be partitioned into blocks, each inducing a subgraph of `G` that contains a
spanning copy of `H`? Kirkpatrick and Hell prove this NP-complete whenever `H` has a connected
component with at least 3 vertices (when every component of `H` has at most 2 vertices, the
problem is solvable in polynomial time via matching).

`H` is not part of the instance: it is the pattern `(m, hs)` (vertices `Fin m`, simple edge list
`hs`), a parameter of the decision problem `perfectHPackingDec m hs`, and the theorem is stated
for every pattern satisfying `ValidPattern`. The question and the well-formedness condition are
those of `WantedExt.Complexity.NPComplete.PartitionIntoIsomorphicSubgraphsWanted` (the `H`-factor
form, where each block's induced subgraph has a spanning subgraph isomorphic to `H`), applied to
the instance with that fixed pattern (`withPattern`); its well-formedness asks `|V| = q|V(H)|`
for a positive integer `q`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PERFECT H-PACKING is NP-complete for every fixed `H` with a connected component of at
least 3 vertices.** Source: Kirkpatrick and Hell (1978); Garey and Johnson (1979), comment to
[GT12]. -/
public theorem_wanted perfectHPacking_npComplete (m : ℕ) (hs : List (ℕ × ℕ))
    (hH : ValidPattern m hs) :
    perfectHPackingDec m hs ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (perfectHPackingDec m hs)

end MetaMathlibExt.Complexity.NPComplete.PerfectHPacking
