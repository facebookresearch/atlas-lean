/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMULTANEOUS INCONGRUENCES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN2] SIMULTANEOUS
INCONGRUENCES;
L. J. Stockmeyer and A. R. Meyer, "Word problems requiring exponential time
(preliminary report)", Proceedings of the 5th Annual ACM Symposium on Theory of
Computing (STOC 1973), 1-9, doi:10.1145/800125.804029.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Int.ModEq

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimultaneousIncongruences

/-!
# SIMULTANEOUS INCONGRUENCES is NP-complete

INSTANCE: a collection `{(a₁, b₁), ..., (aₙ, bₙ)}` of ordered pairs of positive integers, with
`aᵢ ≤ bᵢ` for `1 ≤ i ≤ n`. QUESTION: is there an integer `x` such that, for `1 ≤ i ≤ n`,
`x ≢ aᵢ (mod bᵢ)`?

The collection is a list of pairs `(aᵢ, bᵢ)`; repeated pairs do not change the question.
Incongruence is Mathlib's `Int.ModEq`, negated.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the list of pairs `(aᵢ, bᵢ)`. -/
abbrev SimultaneousIncongruencesInstance := List (ℕ × ℕ)

/-- Well-formedness of an instance: every pair `(aᵢ, bᵢ)` consists of positive integers with
`aᵢ ≤ bᵢ` (so `bᵢ` is positive as well). -/
def WellFormed (i : SimultaneousIncongruencesInstance) : Prop :=
  ∀ p ∈ i, 0 < p.1 ∧ p.1 ≤ p.2

/-- Some integer `x` satisfies `x ≢ aᵢ (mod bᵢ)` for every pair `(aᵢ, bᵢ)`. -/
def SimultaneousIncongruencesFeasible (i : SimultaneousIncongruencesInstance) : Prop :=
  ∃ x : ℤ, ∀ p ∈ i, ¬ x ≡ (p.1 : ℤ) [ZMOD (p.2 : ℤ)]

open Classical in
/-- SIMULTANEOUS INCONGRUENCES as a decision problem over bitstrings. -/
noncomputable def simultaneousIncongruencesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SimultaneousIncongruencesInstance) x with
  | some i => decide (WellFormed i ∧ SimultaneousIncongruencesFeasible i)
  | none => false

/-- **SIMULTANEOUS INCONGRUENCES is NP-complete.** Source: Garey and Johnson (1979), [AN2];
Stockmeyer and Meyer (1973). -/
public theorem_wanted simultaneousIncongruences_npComplete :
    simultaneousIncongruencesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simultaneousIncongruencesDec

end MetaMathlibExt.Complexity.NPComplete.SimultaneousIncongruences
