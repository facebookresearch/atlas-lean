/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE DELETION k-PARTITION is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MINIMUM EDGE DELETION K-PARTITION;
V. Kann, S. Khanna, J. Lagergren and A. Panconesi, "On the hardness of approximating Max k-Cut
and its dual", Chicago J. Theoret. Comput. Sci. 1997, Article 2 (the Min k-Partition problem);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND16] MAX CUT (the case `k = 2`, by
complementing the bound).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeDeletionKPartition

/-!
# EDGE DELETION k-PARTITION is NP-complete

For a fixed number `k ≥ 2` of parts:
INSTANCE: a graph `G = (V, E)`, a positive integer weight `w(e)` for each edge `e ∈ E`, and a
positive integer `K`.
QUESTION: is there a `k`-partition of `V`, i.e., a color assignment `c : V → {1, …, k}`, such
that the weight of the monochromatic edges, `∑ {w(v₁, v₂) : (v₁, v₂) ∈ E, c(v₁) = c(v₂)}`, is at
most `K`?

This is the decision version of MINIMUM EDGE DELETION K-PARTITION (an entry of the Crescenzi-Kann
compendium), the Min k-Partition problem of Kann, Khanna, Lagergren and Panconesi: deleting the
monochromatic edges leaves a `k`-colorable graph. The number `k` of parts is fixed, a parameter
of the language, as in the compendium's comments for `k = 2` and for `k ≥ 3`. Weights are
positive, as in Kann, Khanna, Lagergren and Panconesi. For `k = 2` the
question is MAX CUT [ND16] with the complementary bound (the cut has weight at least
`w(E) - K`). The bound is a positive integer, following the Garey-Johnson convention for decision
versions.

The graph has vertices `0, …, n - 1` and is given by its list of weighted edges `(u, v, w)`:
distinct undirected edges without loops or repeated pairs, as in
`WantedExt.Complexity.NPComplete.DominatingSetWanted`. A color assignment is a list giving each
vertex a color below `k`, as in `WantedExt.Complexity.NPComplete.MaxKCutWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. Weights and the bound use the
canonical binary encoding.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n`, weighted edge list `(u, v, w)` and bound `K`. -/
abbrev EdgeDeletionKPartitionInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- The unweighted edges of an instance. -/
def edges (i : EdgeDeletionKPartitionInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- Well-formedness of an instance: the edges are distinct, in range, without loops or repeated
pairs; every weight is positive; and `0 < K`. -/
def WellFormed (i : EdgeDeletionKPartitionInstance) : Prop :=
  (edges i).Nodup ∧
    (∀ e ∈ edges i, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ edges i) ∧
    (∀ e ∈ i.2.1, 0 < e.2.2) ∧ 0 < i.2.2

/-- The weight of the edges whose endpoints get the same color under `c`. -/
def monochromaticWeight (i : EdgeDeletionKPartitionInstance) (c : List ℕ) : ℕ :=
  ((i.2.1.filter fun e => c.getD e.1 0 = c.getD e.2.1 0).map fun e => e.2.2).sum

/-- Some assignment of colors below `k` to the vertices has monochromatic weight at most `K`. -/
def EdgeDeletionKPartitionFeasible (k : ℕ) (i : EdgeDeletionKPartitionInstance) : Prop :=
  ∃ c : List ℕ, c.length = i.1 ∧ (∀ v < i.1, c.getD v 0 < k) ∧ monochromaticWeight i c ≤ i.2.2

open Classical in
/-- EDGE DELETION k-PARTITION, for the fixed `k`, as a decision problem over bitstrings. -/
noncomputable def edgeDeletionKPartitionDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeDeletionKPartitionInstance) x with
  | some i => decide (WellFormed i ∧ EdgeDeletionKPartitionFeasible k i)
  | none => false

/-- **EDGE DELETION k-PARTITION is NP-complete for every fixed `k ≥ 2`.** Source: Crescenzi and
Kann, MINIMUM EDGE DELETION K-PARTITION; Kann, Khanna, Lagergren and Panconesi (1997); Garey and
Johnson (1979), [ND16]. -/
public theorem_wanted edgeDeletionKPartition_npComplete (k : ℕ) (_hk : 2 ≤ k) :
    edgeDeletionKPartitionDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (edgeDeletionKPartitionDec k)

end MetaMathlibExt.Complexity.NPComplete.EdgeDeletionKPartition
