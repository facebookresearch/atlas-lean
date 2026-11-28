/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXPECTED RETRIEVAL COST with a fixed number of sectors: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR4] EXPECTED RETRIEVAL COST, p. 227,
comment: "NP-complete and solvable in pseudo-polynomial time for each fixed m ≥ 2";
R. A. Cody and E. G. Coffman, Jr., "Record allocation for minimizing expected retrieval costs on
drum-like storage devices", Journal of the ACM 23 (1976), 103-115, doi:10.1145/321921.321933;
Garey and Johnson (1979), problem [SP19] MINIMUM SUM OF SQUARES, p. 225, comment: "NP-complete in
the ordinary sense and solvable in pseudo-polynomial time for any fixed K".
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ExpectedRetrievalCostDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCostFixedSectors

open MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCost (toRat retrievalCost)

/-- An instance (for a fixed number `m` of sectors): the records' probabilities `p(r)` as pairs
`(a, b)` meaning `a / b`, and the bound `K` as a pair `(a, b)` meaning `a / b`. -/
abbrev ExpectedRetrievalCostFixedSectorsInstance := List (ℕ × ℕ) × (ℕ × ℕ)

/-- Well-formedness of an instance: every probability is a fraction `a / b` with `0 < b` and
`a ≤ b` (so it lies in `[0, 1]`), the probabilities sum to `1`, and the bound `K = a / b` has
`0 < b` and `0 < a` (so `K` is a positive rational). -/
def WellFormed (i : ExpectedRetrievalCostFixedSectorsInstance) : Prop :=
  (∀ q ∈ i.1, 0 < q.2 ∧ q.1 ≤ q.2) ∧ (i.1.map toRat).sum = 1 ∧ 0 < i.2.2 ∧ 0 < i.2.1

/-- Some allocation of the records to the `m` sectors, with every sector nonempty, has expected
retrieval cost at most `K` (the parent's `retrievalCost` of the records with `m` sectors; it
does not read the third component, the parent's integer bound, set to `0` here). -/
def ExpectedRetrievalCostFixedSectorsFeasible (m : ℕ)
    (i : ExpectedRetrievalCostFixedSectorsInstance) : Prop :=
  ∃ f : Fin i.1.length → Fin m, Function.Surjective f ∧
    retrievalCost (i.1, m, 0) f ≤ toRat i.2

open Classical in
/-- EXPECTED RETRIEVAL COST with `m` sectors as a decision problem over bitstrings. -/
noncomputable def expectedRetrievalCostFixedSectorsDec (m : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExpectedRetrievalCostFixedSectorsInstance) x with
  | some i => decide (WellFormed i ∧ ExpectedRetrievalCostFixedSectorsFeasible m i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCostFixedSectors
