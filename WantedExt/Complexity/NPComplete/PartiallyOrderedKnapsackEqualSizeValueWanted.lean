/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIALLY ORDERED KNAPSACK with `s(u) = v(u)` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP12] PARTIALLY ORDERED KNAPSACK,
comment (p. 248): "NP-complete in the strong sense, even if `s(u) = v(u)` for all `u ∈ U`"
(reference of the entry: [Garey and Johnson, ——], unpublished; transformation from CLIQUE);
D. S. Johnson and K. A. Niemi, "On knapsacks, partitions, and a new dynamic programming
technique for trees", Mathematics of Operations Research 8 (1983), 1-14,
doi:10.1287/moor.8.1.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PartiallyOrderedKnapsackWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartiallyOrderedKnapsackEqualSizeValue

open PartiallyOrderedKnapsack (PartiallyOrderedKnapsackInstance PartiallyOrderedKnapsackFeasible)

/-!
# PARTIALLY ORDERED KNAPSACK with `s(u) = v(u)` is NP-complete

INSTANCE: a finite set `U`, a partial order `<` on `U`, for each `u ∈ U` a size `s(u) ∈ Z⁺` and
a value `v(u) ∈ Z⁺` with `s(u) = v(u)`, and positive integers `B` and `K`.
QUESTION: is there a subset `U' ⊆ U` such that if `u ∈ U'` and `u' < u`, then `u' ∈ U'`, and
such that `∑_{u ∈ U'} s(u) ≤ B` and `∑_{u ∈ U'} v(u) ≥ K`?

This is the restriction of [MP12] PARTIALLY ORDERED KNAPSACK
(`WantedExt.Complexity.NPComplete.PartiallyOrderedKnapsackWanted`) stated in its comment. The
instance type (the elements as `(s(u), v(u))` pairs, the order pairs, `B`, `K`),
`PartiallyOrderedKnapsack.WellFormed` (the listed pairs form a strict partial order on the
elements, positive sizes, values and bounds) and `PartiallyOrderedKnapsackFeasible` are reused
unchanged; the restriction `s(u) = v(u)` is added to well-formedness. The problem is NP-complete
in the strong sense, so the binary encoding of the numbers is immaterial.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed PARTIALLY ORDERED KNAPSACK instance in which
every element has `s(u) = v(u)`. -/
def WellFormed (i : PartiallyOrderedKnapsackInstance) : Prop :=
  PartiallyOrderedKnapsack.WellFormed i ∧ ∀ u ∈ i.1, u.1 = u.2

open Classical in
/-- PARTIALLY ORDERED KNAPSACK with `s(u) = v(u)` as a decision problem over bitstrings. -/
noncomputable def partiallyOrderedKnapsackEqualSizeValueDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartiallyOrderedKnapsackInstance) x with
  | some i => decide (WellFormed i ∧ PartiallyOrderedKnapsackFeasible i)
  | none => false

/-- **PARTIALLY ORDERED KNAPSACK with `s(u) = v(u)` is NP-complete.**
Source: Garey and Johnson (1979), [MP12], comment; Johnson and Niemi (1983). -/
public theorem_wanted partiallyOrderedKnapsackEqualSizeValue_npComplete :
    partiallyOrderedKnapsackEqualSizeValueDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partiallyOrderedKnapsackEqualSizeValueDec

end MetaMathlibExt.Complexity.NPComplete.PartiallyOrderedKnapsackEqualSizeValue
