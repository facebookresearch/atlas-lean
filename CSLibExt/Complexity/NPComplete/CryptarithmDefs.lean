/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CRYPTARITHM: definitions

Source:
D. Eppstein, "On the NP-completeness of cryptarithms", ACM SIGACT News 18(3) (1987), 38-40,
doi:10.1145/24658.24662.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Set.Operations

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Cryptarithm

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

end MetaMathlibExt.Complexity.NPComplete.Cryptarithm
