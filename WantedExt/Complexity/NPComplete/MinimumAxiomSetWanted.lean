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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Function.Iterate

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

/-- An instance: the number `|S|` of sentences (sentences `0, ..., |S| - 1`), the true sentences
`T`, the implication relation `R` (pairs `(A, s)`, the premises `A` as a list), and the bound
`K`. -/
abbrev MinimumAxiomSetInstance := ℕ × List ℕ × List (List ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: every true sentence, premise and conclusion is a sentence
(`< |S|`), and `0 < K ≤ |S|`. -/
def WellFormed (i : MinimumAxiomSetInstance) : Prop :=
  (∀ x ∈ i.2.1, x < i.1) ∧ (∀ r ∈ i.2.2.1, (∀ x ∈ r.1, x < i.1) ∧ r.2 < i.1) ∧
    0 < i.2.2.2 ∧ i.2.2.2 ≤ i.1

/-- One derivation round: the sentences of `X`, together with the conclusion `s` of every pair
`(A, s) ∈ R` whose premises `A` all lie in `X`. -/
def derive (R : List (List ℕ × ℕ)) (X : Finset ℕ) : Finset ℕ :=
  X ∪ ((R.filter fun r => ∀ x ∈ r.1, x ∈ X).map Prod.snd).toFinset

/-- Some set `S₀` of at most `K` true sentences reaches exactly `T` after `n ≥ 1` derivation
rounds. -/
def MinimumAxiomSetFeasible (i : MinimumAxiomSetInstance) : Prop :=
  ∃ S₀ : Finset ℕ, (∀ x ∈ S₀, x ∈ i.2.1) ∧ S₀.card ≤ i.2.2.2 ∧
    ∃ n, 0 < n ∧ (derive i.2.2.1)^[n] S₀ = i.2.1.toFinset

open Classical in
/-- MINIMUM AXIOM SET as a decision problem over bitstrings. -/
noncomputable def minimumAxiomSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumAxiomSetInstance) x with
  | some i => decide (WellFormed i ∧ MinimumAxiomSetFeasible i)
  | none => false

/-- **MINIMUM AXIOM SET is NP-complete.** Source: Garey and Johnson (1979), [LO17];
Pudlák (1975). -/
public theorem_wanted minimumAxiomSet_npComplete :
    minimumAxiomSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumAxiomSetDec

end MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSet
