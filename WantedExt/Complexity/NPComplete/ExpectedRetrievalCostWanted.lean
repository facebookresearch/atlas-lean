/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXPECTED RETRIEVAL COST is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR4] EXPECTED RETRIEVAL COST;
R. A. Cody and E. G. Coffman, Jr., "Record allocation for minimizing expected retrieval costs on
drum-like storage devices", Journal of the ACM 23 (1976), 103-115, doi:10.1145/321921.321933.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCost

/-!
# EXPECTED RETRIEVAL COST is NP-complete

INSTANCE: a set `R` of records, a rational probability `p(r) ∈ [0, 1]` for each `r ∈ R`, with
`∑_{r ∈ R} p(r) = 1`, a number `m` of sectors, and a positive integer `K`. QUESTION: is there a
partition of `R` into disjoint subsets `R₁, R₂, …, Rₘ` such that, if `p(Rᵢ) = ∑_{r ∈ Rᵢ} p(r)`
and the "latency cost" `d(i, j)` is defined to be `j - i - 1` if `1 ≤ i < j ≤ m` and to be
`m - i + j - 1` if `1 ≤ j ≤ i ≤ m`, then the sum over all ordered pairs `i, j`,
`1 ≤ i, j ≤ m`, of `p(Rᵢ) · p(Rⱼ) · d(i, j)` is at most `K`?

The partition is given by the map `f : R → Fin m` sending each record to its sector, so
`Rᵢ = f⁻¹(i)`; `f` is surjective because the blocks of a partition are nonempty (so a
yes-instance has `m ≤ |R|`). Sectors are indexed from `0` here, which leaves both
cases of `d` unchanged. A rational probability `a / b` is encoded as a pair of naturals
`(a, b)` with `0 < b`; the cost is a rational number compared with the integer `K`. Numbers use
the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: record weights `p(r)` as pairs `(a, b)` read as `a / b` (`0` when `b = 0`),
probabilities for well-formed instances, the number `m` of sectors, and a natural bound `K`
(positive for well-formed instances). -/
abbrev ExpectedRetrievalCostInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- The rational `a / b` encoded by the pair `(a, b)`. -/
def toRat (q : ℕ × ℕ) : ℚ := (q.1 : ℚ) / q.2

/-- The latency cost `d(i, j)`: `j - i - 1` if `i < j`, and `m - i + j - 1` if `j ≤ i`. -/
def latency (m : ℕ) (i j : Fin m) : ℕ :=
  if (i : ℕ) < j then j - i - 1 else m - i + j - 1

/-- `p(Rᵢ)`: the sum of the listed weights of the records that `f` places in sector `i` (a
probability for normalised weights, as `WellFormed` requires). -/
def sectorProb (inst : ExpectedRetrievalCostInstance) (f : Fin inst.1.length → Fin inst.2.1)
    (i : Fin inst.2.1) : ℚ :=
  ∑ r : Fin inst.1.length, if f r = i then toRat inst.1[r] else 0

/-- The weighted latency sum `∑_{i, j} p(Rᵢ) · p(Rⱼ) · d(i, j)` of the allocation `f`, the
expected retrieval cost for normalised record probabilities. -/
def retrievalCost (inst : ExpectedRetrievalCostInstance)
    (f : Fin inst.1.length → Fin inst.2.1) : ℚ :=
  ∑ i : Fin inst.2.1, ∑ j : Fin inst.2.1,
    sectorProb inst f i * sectorProb inst f j * latency inst.2.1 i j

/-- Well-formedness of an instance: every probability is a fraction `a / b` with `0 < b` and
`a ≤ b` (so it lies in `[0, 1]`), the probabilities sum to `1`, and `0 < K`. -/
def WellFormed (inst : ExpectedRetrievalCostInstance) : Prop :=
  (∀ q ∈ inst.1, 0 < q.2 ∧ q.1 ≤ q.2) ∧ (inst.1.map toRat).sum = 1 ∧ 0 < inst.2.2

/-- Some allocation of the records to the `m` sectors, with every sector nonempty, has weighted
latency cost `retrievalCost` at most `K` (the expected retrieval cost for well-formed
instances). -/
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

/-- **EXPECTED RETRIEVAL COST is NP-complete.** Source: Garey and Johnson (1979), [SR4]; Cody
and Coffman (1976). -/
public theorem_wanted expectedRetrievalCost_npComplete :
    expectedRetrievalCostDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L expectedRetrievalCostDec

end MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCost
