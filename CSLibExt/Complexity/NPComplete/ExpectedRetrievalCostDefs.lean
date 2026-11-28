/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXPECTED RETRIEVAL COST: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR4] EXPECTED RETRIEVAL COST;
R. A. Cody and E. G. Coffman, Jr., "Record allocation for minimizing expected retrieval costs on
drum-like storage devices", Journal of the ACM 23 (1976), 103-115, doi:10.1145/321921.321933.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCost

/-- An instance: the records' probabilities `p(r)` as pairs `(a, b)` meaning `a / b`, the number
`m` of sectors, and the bound `K`. -/
abbrev ExpectedRetrievalCostInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- The rational `a / b` encoded by the pair `(a, b)`. -/
def toRat (q : ℕ × ℕ) : ℚ := (q.1 : ℚ) / q.2

/-- The latency cost `d(i, j)`: `j - i - 1` if `i < j`, and `m - i + j - 1` if `j ≤ i`. -/
def latency (m : ℕ) (i j : Fin m) : ℕ :=
  if (i : ℕ) < j then j - i - 1 else m - i + j - 1

/-- `p(Rᵢ)`: the total probability of the records that `f` places in sector `i`. -/
def sectorProb (inst : ExpectedRetrievalCostInstance) (f : Fin inst.1.length → Fin inst.2.1)
    (i : Fin inst.2.1) : ℚ :=
  ∑ r : Fin inst.1.length, if f r = i then toRat inst.1[r] else 0

/-- The expected retrieval cost `∑_{i, j} p(Rᵢ) · p(Rⱼ) · d(i, j)` of the allocation `f`. -/
def retrievalCost (inst : ExpectedRetrievalCostInstance)
    (f : Fin inst.1.length → Fin inst.2.1) : ℚ :=
  ∑ i : Fin inst.2.1, ∑ j : Fin inst.2.1,
    sectorProb inst f i * sectorProb inst f j * latency inst.2.1 i j

/-- Well-formedness of an instance: every probability is a fraction `a / b` with `0 < b` and
`a ≤ b` (so it lies in `[0, 1]`), the probabilities sum to `1`, and `0 < K`. -/
def WellFormed (inst : ExpectedRetrievalCostInstance) : Prop :=
  (∀ q ∈ inst.1, 0 < q.2 ∧ q.1 ≤ q.2) ∧ (inst.1.map toRat).sum = 1 ∧ 0 < inst.2.2

/-- Some allocation of the records to the `m` sectors, with every sector nonempty, has expected
retrieval cost at most `K`. -/
def ExpectedRetrievalCostFeasible (inst : ExpectedRetrievalCostInstance) : Prop :=
  ∃ f : Fin inst.1.length → Fin inst.2.1, Function.Surjective f ∧ retrievalCost inst f ≤ inst.2.2

open Classical in
/-- EXPECTED RETRIEVAL COST as a decision problem over bitstrings. -/
noncomputable def expectedRetrievalCostDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExpectedRetrievalCostInstance) x with
  | some i => decide (WellFormed i ∧ ExpectedRetrievalCostFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCost
