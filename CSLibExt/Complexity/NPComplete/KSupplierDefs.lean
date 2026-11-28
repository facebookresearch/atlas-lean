/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-SUPPLIER: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MINIMUM K-SUPPLIER (decision version);
D. S. Hochbaum and D. B. Shmoys, "A unified approach to approximation algorithms for bottleneck
problems", Journal of the ACM 33(3) (1986), 533-550, doi:10.1145/5925.5933 (weighted center and
supplier problems; "for all of the problems we consider, this decision problem is
NP-complete");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND50] MIN-MAX MULTICENTER, comment
(the vertex `p`-center variant, transformation from DOMINATING SET [GT2]; O. Kariv and
S. L. Hakimi, SIAM J. Appl. Math. 37 (1979), 513-538).
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KSupplier

/-- An instance: vertex count `n`, distance matrix, construction costs `c`, usage weights `w`,
cost bound `L`, and bound `K`. -/
abbrev KSupplierInstance := ℕ × List (List ℕ) × List ℕ × List ℕ × ℕ × ℕ

/-- The distance `d(a, b)`, read from the matrix. -/
def distance (i : KSupplierInstance) (a b : ℕ) : ℕ :=
  (i.2.1.getD a []).getD b 0

/-- Well-formedness of an instance: an `n × n` distance matrix that is symmetric, has zero
diagonal and satisfies the triangle inequality, cost and weight lists of length `n`, and
`0 < K`. -/
def WellFormed (i : KSupplierInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    i.2.2.1.length = i.1 ∧ i.2.2.2.1.length = i.1 ∧
    (∀ a < i.1, distance i a a = 0) ∧
    (∀ a < i.1, ∀ b < i.1, distance i a b = distance i b a) ∧
    (∀ a < i.1, ∀ b < i.1, ∀ c < i.1, distance i a c ≤ distance i a b + distance i b c) ∧
    0 < i.2.2.2.2.2

/-- A supplier set of total construction cost at most `L` such that every vertex `v` has a
supplier `s` with `w(v) · d(v, s) ≤ K`. -/
def KSupplierFeasible (i : KSupplierInstance) : Prop :=
  ∃ S : Finset ℕ, (∀ s ∈ S, s < i.1) ∧ ∑ s ∈ S, i.2.2.1.getD s 0 ≤ i.2.2.2.2.1 ∧
    ∀ v < i.1, ∃ s ∈ S, i.2.2.2.1.getD v 0 * distance i v s ≤ i.2.2.2.2.2

open Classical in
/-- K-SUPPLIER as a decision problem over bitstrings. -/
noncomputable def kSupplierDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KSupplierInstance) x with
  | some i => decide (WellFormed i ∧ KSupplierFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KSupplier
