/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXPECTED COMPONENT SUM: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP18] EXPECTED COMPONENT SUM,
pp. 224-225 ("Reference: [Garey and Johnson, ——]. Transformation from X3C. The problem is due
to [Witsenhausen, 1978] and corresponds to finding a partition that maximizes the expected
value of the largest component sum, assuming all sets in the partition are equally likely.").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSum

/-- An instance: the dimension `m`, the vectors of `C` (each a list of `m` entries), the number
`K` of parts and the bound `B`. -/
abbrev ExpectedComponentSumInstance := ℕ × List (List ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: every vector has `m` entries, and `K` and `B` are
positive. -/
def WellFormed (i : ExpectedComponentSumInstance) : Prop :=
  (∀ v ∈ i.2.1, v.length = i.1) ∧ 0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- The component sum `∑_{k} max_{j < m} (∑_{v ∈ C_k} v_j)` of the partition of the vectors
`C` into the parts `C_k = f⁻¹(k)`. -/
def componentSum (m : ℕ) (C : List (List ℕ)) {K : ℕ} (f : Fin C.length → Fin K) : ℕ :=
  ∑ k : Fin K, Finset.univ.sup fun j : Fin m =>
    ∑ c ∈ Finset.univ.filter (fun c => f c = k), (C.get c).getD j 0

/-- Some partition of `C` into `K` non-empty disjoint sets has component sum at least `B`. -/
def ExpectedComponentSumFeasible (i : ExpectedComponentSumInstance) : Prop :=
  ∃ f : Fin i.2.1.length → Fin i.2.2.1, Function.Surjective f ∧
    i.2.2.2 ≤ componentSum i.1 i.2.1 f

open Classical in
/-- EXPECTED COMPONENT SUM as a decision problem over bitstrings. -/
noncomputable def expectedComponentSumDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExpectedComponentSumInstance) x with
  | some i => decide (WellFormed i ∧ ExpectedComponentSumFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSum
