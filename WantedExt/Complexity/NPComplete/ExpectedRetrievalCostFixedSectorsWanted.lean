/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXPECTED RETRIEVAL COST with a fixed number of sectors is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ExpectedRetrievalCostWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCostFixedSectors

open MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCost (toRat retrievalCost)

/-!
# EXPECTED RETRIEVAL COST with a fixed number of sectors is NP-complete

For a fixed number `m ≥ 2` of sectors:
INSTANCE: a set `R` of records, a rational probability `p(r) ∈ [0, 1]` for each `r ∈ R`, with
`∑_{r ∈ R} p(r) = 1`, and a positive rational bound `K`. QUESTION: is there a partition of `R`
into disjoint subsets `R₁, R₂, …, Rₘ` such that, if `p(Rᵢ) = ∑_{r ∈ Rᵢ} p(r)` and the
"latency cost" `d(i, j)` is defined to be `j - i - 1` if `1 ≤ i < j ≤ m` and to be
`m - i + j - 1` if `1 ≤ j ≤ i ≤ m`, then the sum over all ordered pairs `i, j`, `1 ≤ i, j ≤ m`,
of `p(Rᵢ) · p(Rⱼ) · d(i, j)` is at most `K`?

This is EXPECTED RETRIEVAL COST (`MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCost`)
with the number of sectors a constant `m` of the problem rather than part of the instance; one
`theorem_wanted` states NP-completeness for every fixed `m ≥ 2`. The allocation (a surjective map
`f : R → Fin m`, `Rᵢ = f⁻¹(i)`, so every block of the partition is nonempty) and its cost
(`retrievalCost`) are the parent's.

The bound is rational here, where the parent (following Garey and Johnson's INSTANCE line) takes
a positive integer `K`. For fixed `m` an integer bound loses the problem: since `d(i, i) = m - 1`
and `d(i, j) + d(j, i) = m - 2` for `i ≠ j`, and `∑ p(Rᵢ) = 1`, the cost equals
`(m - 2) / 2 + (m / 2) · ∑ᵢ p(Rᵢ)²`. For `m = 2` it is `p(R₁)² + p(R₂)² ≤ 1`, so every instance
with at least two records would be a yes-instance for every positive integer `K`. With a rational
bound the problem is, by the same identity, MINIMUM SUM OF SQUARES ([SP19]) with `m` parts: for
sizes `s(a) ∈ ℤ⁺` with total `S`, take `p(a) = s(a) / S` and
`K = (m - 2) / 2 + (m / 2) · J / S²`; then `∑ᵢ (∑_{a ∈ Aᵢ} s(a))² ≤ J` exactly when the cost is at
most `K` (a partition meeting `J` with empty parts refines to one with nonempty parts, because
splitting a part lowers the sum of squares). Garey and Johnson record [SP19] as NP-complete for
every fixed number of parts `≥ 2`; for `m = 2` the bound `K = 1/2` asks whether
`p(R₁) = p(R₂) = 1/2`, which is PARTITION. Integer bounds remain instances (`K = a / 1`).
Probabilities and the bound are pairs `(a, b)` of naturals meaning `a / b` with `0 < b`. Numbers
use the binary encoding (the problem is solvable in pseudo-polynomial time for each fixed `m`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **EXPECTED RETRIEVAL COST with a fixed number `m ≥ 2` of sectors is NP-complete.** Source:
Garey and Johnson (1979), [SR4], comment; Cody and Coffman (1976); for the rational bound, Garey
and Johnson (1979), [SP19], comment, through the identity in the module docstring. -/
public theorem_wanted expectedRetrievalCostFixedSectors_npComplete (m : ℕ) (_hm : 2 ≤ m) :
    expectedRetrievalCostFixedSectorsDec m ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (expectedRetrievalCostFixedSectorsDec m)

end MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCostFixedSectors
