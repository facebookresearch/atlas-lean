/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMPARATIVE CONTAINMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP10] COMPARATIVE CONTAINMENT,
p. 223 ("Reference: [Plaisted, 1976]. Transformation from VERTEX COVER.");
D. A. Plaisted, "Some polynomial and integer divisibility problems are NP-hard",
Proc. 17th Annual Symposium on Foundations of Computer Science (FOCS 1976), 264-267,
doi:10.1109/SFCS.1976.29.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ComparativeContainmentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ComparativeContainment

/-!
# COMPARATIVE CONTAINMENT is NP-complete

INSTANCE: two collections `R = {R₁, …, R_k}` and `S = {S₁, …, S_l}` of subsets of a finite set
`X`, weights `w(R_i) ∈ ℤ⁺`, `1 ≤ i ≤ k`, and `w(S_j) ∈ ℤ⁺`, `1 ≤ j ≤ l`. QUESTION: is there a
subset `Y ⊆ X` such that `∑_{Y ⊆ R_i} w(R_i) ≥ ∑_{Y ⊆ S_j} w(S_j)`?

The ground set is `X = Fin n`. Each collection is an indexed list of (subset, weight) pairs,
as `R₁, …, R_k` with one weight per index; a subset is a list of distinct elements of `X`.
Weights use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COMPARATIVE CONTAINMENT is NP-complete.** Source: Garey and Johnson (1979), [SP10];
Plaisted (1976). -/
public theorem_wanted comparativeContainment_npComplete :
    comparativeContainmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L comparativeContainmentDec

end MetaMathlibExt.Complexity.NPComplete.ComparativeContainment
