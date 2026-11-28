/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CRYPTARITHM is NP-complete

Source:
D. Eppstein, "On the NP-completeness of cryptarithms", ACM SIGACT News 18(3) (1987), 38-40,
doi:10.1145/24658.24662.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CryptarithmDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Cryptarithm

/-!
# CRYPTARITHM is NP-complete

INSTANCE: a base `b ≥ 2` and an addition puzzle `w₁ + w₂ = w₃`, where `w₁`, `w₂`, `w₃` are
nonempty words over an alphabet of letters, with at most `b` different letters in the puzzle.
QUESTION: is there a one-to-one correspondence between the letters of the puzzle and base-`b`
digits (not all digits need appear) that makes the sum correct, when each word is read as the
base-`b` numeral whose digits are the digits of its letters?

This is Eppstein's generalized cryptarithm: the base is part of the instance and the puzzle may
contain arbitrarily many different letters, up to the base. Eppstein's puzzle asks only for the
one-to-one correspondence that makes the sum correct; the customary rule against leading zeros,
which he mentions as usual, is not part of this statement.

A letter is a natural number, and a word is the list of its letters, most significant first.
A correspondence is a map `f : ℕ → ℕ` that sends the letters of the puzzle to digits `< b` and
is injective on them; the value of a word is `Nat.ofDigits b` of its digit list, least
significant first.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`; the base is a number in binary encoding.
Undecodable bitstrings, and bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CRYPTARITHM is NP-complete.** Source: Eppstein (1987). -/
public theorem_wanted cryptarithm_npComplete :
    cryptarithmDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cryptarithmDec

end MetaMathlibExt.Complexity.NPComplete.Cryptarithm
