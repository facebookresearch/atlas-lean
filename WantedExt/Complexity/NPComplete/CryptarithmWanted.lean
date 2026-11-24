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
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Set.Operations

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

/-- An instance: the base `b` and the words `w₁`, `w₂`, `w₃` of the puzzle `w₁ + w₂ = w₃`, each
a list of letters, most significant first. -/
abbrev CryptarithmInstance := ℕ × List ℕ × List ℕ × List ℕ

/-- The letters of the puzzle, with repetitions. -/
def letters (i : CryptarithmInstance) : List ℕ :=
  i.2.1 ++ i.2.2.1 ++ i.2.2.2

/-- The value of the word `w` in base `b` when letter `x` stands for the digit `f x`. -/
def wordValue (b : ℕ) (f : ℕ → ℕ) (w : List ℕ) : ℕ :=
  Nat.ofDigits b (w.reverse.map f)

/-- Well-formedness of an instance: the base is at least `2`, the three words are nonempty, and
the puzzle has at most `b` different letters. -/
def WellFormed (i : CryptarithmInstance) : Prop :=
  2 ≤ i.1 ∧ i.2.1 ≠ [] ∧ i.2.2.1 ≠ [] ∧ i.2.2.2 ≠ [] ∧ (letters i).dedup.length ≤ i.1

/-- Some one-to-one correspondence between the letters of the puzzle and base-`b` digits makes
the sum `w₁ + w₂ = w₃` correct. -/
def CryptarithmFeasible (i : CryptarithmInstance) : Prop :=
  ∃ f : ℕ → ℕ, (∀ x ∈ letters i, f x < i.1) ∧ Set.InjOn f {x | x ∈ letters i} ∧
    wordValue i.1 f i.2.1 + wordValue i.1 f i.2.2.1 = wordValue i.1 f i.2.2.2

open Classical in
/-- CRYPTARITHM as a decision problem over bitstrings. -/
noncomputable def cryptarithmDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CryptarithmInstance) x with
  | some i => decide (WellFormed i ∧ CryptarithmFeasible i)
  | none => false

/-- **CRYPTARITHM is NP-complete.** Source: Eppstein (1987). -/
public theorem_wanted cryptarithm_npComplete :
    cryptarithmDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cryptarithmDec

end MetaMathlibExt.Complexity.NPComplete.Cryptarithm
