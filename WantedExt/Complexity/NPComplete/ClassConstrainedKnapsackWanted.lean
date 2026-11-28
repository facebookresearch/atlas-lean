/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLASS-CONSTRAINED KNAPSACK is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), problem MAXIMUM CLASS-CONSTRAINED KNAPSACK;
H. Shachnai and T. Tamir, "On two class-constrained versions of the multiple knapsack
problem", Algorithmica 29 (2001), 442-467, doi:10.1007/s004530010057 (the class-constrained
multiple knapsack problem, CMKP, is NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ClassConstrainedKnapsackDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClassConstrainedKnapsack

/-!
# CLASS-CONSTRAINED KNAPSACK is NP-complete

INSTANCE: `n` set sizes given by an `n`-vector `U ∈ ℕⁿ`, `m` knapsacks with volumes and
numbers of compartments given by two `m`-vectors `V ∈ ℕᵐ`, `C ∈ ℕᵐ`, such that
`∑ᵢ Uᵢ = ∑ⱼ Vⱼ`, and a positive integer `K`.
QUESTION: is there a placement of the set elements into the knapsacks, given by two `n × m`
matrices `I ∈ {0, 1}^{n × m}` and `Q ∈ ℕ^{n × m}`, such that `∑ᵢ Q_{i,j} ≤ Vⱼ` and
`∑ᵢ I_{i,j} ≤ Cⱼ` for every `j`, `∑ⱼ Q_{i,j} ≤ Uᵢ` for every `i`, and `I_{i,j} = 0 ⇒ Q_{i,j} = 0`
for every `(i, j)`, with total number of packed elements `∑ᵢ ∑ⱼ Q_{i,j}` at least `K`?

Set `i` has `Uᵢ` elements of unit size and one type; `Q_{i,j}` elements of set `i` go into
knapsack `j`, which then spends one of its `Cⱼ` compartments on set `i` (`I_{i,j} = 1`). The
entries of `I` are booleans (`true` for `1`). The volumes need not be distinct (the source's
"different volumes" means per-knapsack volumes, as in Shachnai and Tamir, Section 1.1).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. All numbers use the binary
encoding.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CLASS-CONSTRAINED KNAPSACK is NP-complete.** Source: Crescenzi and Kann, MAXIMUM
CLASS-CONSTRAINED KNAPSACK; Shachnai and Tamir (2001). -/
public theorem_wanted classConstrainedKnapsack_npComplete :
    classConstrainedKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L classConstrainedKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.ClassConstrainedKnapsack
