/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BICONNECTIVITY AUGMENTATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND18] BICONNECTIVITY AUGMENTATION;
K. P. Eswaran and R. E. Tarjan, "Augmentation problems", SIAM Journal on Computing 5 (1976),
653-665, doi:10.1137/0205044.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BiconnectivityAugmentation

/-!
# BICONNECTIVITY AUGMENTATION is NP-complete

Given a graph `G = (V, E)`, a weight `w({u, v}) ∈ Z⁺` for each unordered pair `{u, v}` of
vertices from `V`, and a positive integer `B`, is there a set `E'` of unordered pairs of
vertices from `V` such that `∑_{e ∈ E'} w(e) ≤ B` and the graph `G' = (V, E ∪ E')` is
biconnected, i.e., cannot be disconnected by removing a single vertex?

The vertices are `0, ..., n - 1` with `n ≥ 3`; biconnectivity is
`SimpleGraph.IsVertexConnected 2` (`MathlibExt`): more than two vertices, connected, and
connected after deleting any one vertex. The weights are an `n × n` symmetric matrix whose
off-diagonal entries are positive (the diagonal is never used). `E'` is a list of pairs of
distinct vertices; listing a pair twice only adds its weight twice.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n`, edge list of `G`, weight matrix `w` (row `u`, column `v`
holds `w({u, v})`), and the bound `B`. -/
abbrev BiconnectivityAugmentationInstance := ℕ × List (ℕ × ℕ) × List (List ℕ) × ℕ

/-- The weight of the pair `{u, v}`. -/
def weight (w : List (List ℕ)) (u v : ℕ) : ℕ := (w.getD u []).getD v 0

/-- Well-formedness of an instance: `n ≥ 3`; the edge list is simple (in range, no loops, no
repeated edge in either orientation); `w` is an `n × n` symmetric matrix with positive
off-diagonal entries; and `B` is positive. -/
def WellFormed (i : BiconnectivityAugmentationInstance) : Prop :=
  3 ≤ i.1 ∧ i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.1 ∧ (∀ row ∈ i.2.2.1, row.length = i.1) ∧
    (∀ u < i.1, ∀ v < i.1, weight i.2.2.1 u v = weight i.2.2.1 v u) ∧
    (∀ u < i.1, ∀ v < i.1, u ≠ v → 0 < weight i.2.2.1 u v) ∧ 0 < i.2.2.2

/-- Some list `E'` of pairs of distinct vertices has total weight at most `B`, and adding its
pairs to `G` gives a biconnected graph. -/
def BiconnectivityAugmentationFeasible (i : BiconnectivityAugmentationInstance) : Prop :=
  ∃ E' : List (ℕ × ℕ), (∀ e ∈ E', e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
    (E'.map fun e => weight i.2.2.1 e.1 e.2).sum ≤ i.2.2.2 ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1 ++ E')).IsVertexConnected 2

open Classical in
/-- BICONNECTIVITY AUGMENTATION as a decision problem over bitstrings. -/
noncomputable def biconnectivityAugmentationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BiconnectivityAugmentationInstance) x with
  | some i => decide (WellFormed i ∧ BiconnectivityAugmentationFeasible i)
  | none => false

/-- **BICONNECTIVITY AUGMENTATION is NP-complete.** Source: Garey and Johnson (1979),
[ND18]; Eswaran and Tarjan (1976). -/
public theorem_wanted biconnectivityAugmentation_npComplete :
    biconnectivityAugmentationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L biconnectivityAugmentationDec

end MetaMathlibExt.Complexity.NPComplete.BiconnectivityAugmentation
