/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HIERARCHICAL-TREE CLUSTERING (ℓ₁ ultrametric fitting) is NP-complete

Source:
M. Křivánek and J. Morávek, "NP-hard problems in hierarchical-tree clustering", Acta
Informatica 23 (1986), 311-323, doi:10.1007/BF00289116;
M. Křivánek, "The complexity of ultrametric partitions on graphs", Information Processing
Letters 27 (1988), 265-270, doi:10.1016/0020-0190(88)90090-7, problem (P6).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Bioinformatics.Phylogenetics.Splits
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HierarchicalTreeClustering

open Cslib.Bioinformatics.Phylogenetics.Splits (IsUltrametric)

/-!
# HIERARCHICAL-TREE CLUSTERING (ℓ₁ ultrametric fitting) is NP-complete

INSTANCE: a finite set `X = {x₁, …, xₙ}` with a dissimilarity `w` on `X` (symmetric, and
`w(x, y) = 0` exactly when `x = y`), and a positive integer `K`.
QUESTION: is there an ultrametric `u` on `X` with
`σ(u, w) = ∑_{x < y} |u(x, y) - w(x, y)| ≤ K`?

This is problem (P6) of Křivánek (1988), who records that its NP-completeness was proved by
Křivánek and Morávek (1986). An ultrametric is a metric `u` with
`u(x, z) ≤ max {u(x, y), u(y, z)}`; it is CSLib's
`Cslib.Bioinformatics.Phylogenetics.Splits.IsUltrametric` (symmetric, zero on the diagonal,
positive off the diagonal, three-point condition), with real values.

The objects are `Fin n` and `w` is given by the rows of an `n × n` matrix of natural numbers in
binary encoding. Křivánek states the problem for positive rational dissimilarities; an instance
with rational `w` and integer `K` is equivalent to the integer instance obtained by multiplying
`w` and `K` by a common denominator. Since `w` is integral, some optimal `u` takes its values
in the range of `w` (ℓ₁ isotonic regression over the clusters of `u`), so real, rational and
integer ultrametrics give the same answer.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the rows of the dissimilarity matrix `w` and the bound `K`. -/
abbrev HierarchicalTreeClusteringInstance := List (List ℕ) × ℕ

/-- The entry `w(a, b)` of the matrix. -/
def entry (i : HierarchicalTreeClusteringInstance) (a b : ℕ) : ℕ :=
  (i.1.getD a []).getD b 0

/-- Well-formedness of an instance: the matrix is square, symmetric, zero exactly on the
diagonal, and `K` is positive. -/
def WellFormed (i : HierarchicalTreeClusteringInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.1.length) ∧
    (∀ a < i.1.length, ∀ b < i.1.length,
      (entry i a b = 0 ↔ a = b) ∧ entry i a b = entry i b a) ∧ 0 < i.2

/-- Some ultrametric `u` on `Fin n` has `∑_{x < y} |u(x, y) - w(x, y)| ≤ K`. -/
def HierarchicalTreeClusteringFeasible (i : HierarchicalTreeClusteringInstance) : Prop :=
  ∃ u : Fin i.1.length → Fin i.1.length → ℝ, IsUltrametric u ∧
    ∑ x : Fin i.1.length, ∑ y ∈ Finset.univ.filter (x < ·),
      |u x y - (entry i x y : ℝ)| ≤ i.2

open Classical in
/-- HIERARCHICAL-TREE CLUSTERING as a decision problem over bitstrings. -/
noncomputable def hierarchicalTreeClusteringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HierarchicalTreeClusteringInstance) x with
  | some i => decide (WellFormed i ∧ HierarchicalTreeClusteringFeasible i)
  | none => false

/-- **HIERARCHICAL-TREE CLUSTERING (ℓ₁ ultrametric fitting) is NP-complete.** Source: Křivánek
and Morávek (1986); Křivánek (1988), problem (P6). -/
public theorem_wanted hierarchicalTreeClustering_npComplete :
    hierarchicalTreeClusteringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hierarchicalTreeClusteringDec

end MetaMathlibExt.Complexity.NPComplete.HierarchicalTreeClustering
