/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM AXIOM SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO17] MINIMUM AXIOM
SET;
P. Pudlák, "Polynomially complete problems in the logic of automated
discovery", Mathematical Foundations of Computer Science 1975, Lecture Notes in
Computer Science 32, Springer (1975), 358-361, doi:10.1007/3-540-07389-2_221.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumAxiomSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSet

/-!
# MINIMUM AXIOM SET is NP-complete

INSTANCE: a finite set `S` of "sentences", a subset `T ⊆ S` of "true sentences", an
"implication relation" `R` consisting of pairs `(A, s)` where `A ⊆ S` and `s ∈ S`, and a
positive integer `K ≤ |S|`. QUESTION: is there a subset `S₀ ⊆ T` with `|S₀| ≤ K` and a
positive integer `n` such that, if we define `Sᵢ`, `1 ≤ i ≤ n`, to consist of exactly those
`s ∈ S` for which either `s ∈ Sᵢ₋₁` or there exists a `U ⊆ Sᵢ₋₁` such that `(U, s) ∈ R`, then
`Sₙ = T`?

The sentences are `0, ..., |S| - 1`; `T` is given as a list of sentences and each pair of `R` as
a list of premises with a conclusion. One round `Sᵢ₋₁ ↦ Sᵢ` is `derive R`, and `Sₙ` is its
`n`-th iterate from `S₀`. As in the source, the question asks for some round `n ≥ 1` with
`Sₙ = T`; when `T` is closed under `R` (the intended reading of "true sentences") this is the
same as the closure of `S₀` under `R` being `T`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM AXIOM SET is NP-complete.** Source: Garey and Johnson (1979), [LO17];
Pudlák (1975). -/
public theorem_wanted minimumAxiomSet_npComplete :
    minimumAxiomSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumAxiomSetDec

end MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSet
