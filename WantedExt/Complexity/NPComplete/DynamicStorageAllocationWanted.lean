/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DYNAMIC STORAGE ALLOCATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR2] DYNAMIC STORAGE ALLOCATION,
p. 226 (reference: [Stockmeyer, 1976b], a private communication; transformation from
3-PARTITION).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DynamicStorageAllocationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DynamicStorageAllocation

/-!
# DYNAMIC STORAGE ALLOCATION is NP-complete

INSTANCE: a set `A` of items to be stored, each `a ∈ A` having a size `s(a) ∈ ℤ⁺`, an arrival
time `r(a) ∈ ℤ₀⁺`, and a departure time `d(a) ∈ ℤ⁺`, and a positive integer storage size `D`.
QUESTION: is there a feasible allocation of storage for `A`, i.e., a function
`σ : A → {1, 2, ..., D}` such that for every `a ∈ A` the allocated storage interval
`I(a) = [σ(a), σ(a) + s(a) - 1]` is contained in `[1, D]` and such that, for all `a, a' ∈ A`,
if `I(a) ∩ I(a')` is nonempty then either `d(a) ≤ r(a')` or `d(a') ≤ r(a)`?

The items are a list of records `(s(a), r(a), d(a))`, indexed by `Fin m`; equal records are
different items. `I(a)` is the integer interval `Finset.Icc σ(a) (σ(a) + s(a) - 1)`. The last
condition is required for distinct items `a ≠ a'` (for `a = a'` it would ask `d(a) ≤ r(a)`,
since `I(a)` is nonempty). As in the source, `r(a) < d(a)` is not required. Numbers are in
binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DYNAMIC STORAGE ALLOCATION is NP-complete.** Source: Garey and Johnson (1979), [SR2]
(attributed there to Stockmeyer, private communication). -/
public theorem_wanted dynamicStorageAllocation_npComplete :
    dynamicStorageAllocationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dynamicStorageAllocationDec

end MetaMathlibExt.Complexity.NPComplete.DynamicStorageAllocation
