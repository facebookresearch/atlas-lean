/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM AXIOM SET: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO17] MINIMUM AXIOM
SET;
P. Pudlák, "Polynomially complete problems in the logic of automated
discovery", Mathematical Foundations of Computer Science 1975, Lecture Notes in
Computer Science 32, Springer (1975), 358-361, doi:10.1007/3-540-07389-2_221.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Function.Iterate

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSet

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

end MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSet
