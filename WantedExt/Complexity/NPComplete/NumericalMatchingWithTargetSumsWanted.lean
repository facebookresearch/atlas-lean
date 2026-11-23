/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NUMERICAL MATCHING WITH TARGET SUMS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP17] NUMERICAL MATCHING WITH
TARGET SUMS, p. 224 ("Reference: Transformation from NUMERICAL 3-DIMENSIONAL MATCHING.
Comment: NP-complete in the strong sense, but solvable in polynomial time if
B₁ = B₂ = ⋯ = B_m.").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NumericalMatchingWithTargetSums

/-!
# NUMERICAL MATCHING WITH TARGET SUMS is NP-complete

INSTANCE: disjoint sets `X` and `Y`, each containing `m` elements, a size `s(a) ∈ ℤ⁺` for each
element `a ∈ X ∪ Y`, and a target vector `⟨B₁, B₂, …, B_m⟩` with positive integer entries.
QUESTION: can `X ∪ Y` be partitioned into `m` disjoint sets `A₁, A₂, …, A_m`, each containing
exactly one element from each of `X` and `Y`, such that, for `1 ≤ i ≤ m`,
`∑_{a ∈ A_i} s(a) = B_i`?

The elements of `X` and of `Y` are each indexed by `Fin m`, one per listed size. A partition
of the stated kind is `A_k = {x_{σ k}, y_{τ k}}` for permutations `σ` and `τ` of `Fin m`.
NP-complete in the strong sense; all numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the sizes `s(x₁), …, s(x_m)` of the elements of `X`, the sizes
`s(y₁), …, s(y_m)` of the elements of `Y`, and the targets `B₁, …, B_m`. -/
abbrev NumericalMatchingWithTargetSumsInstance := List ℕ × List ℕ × List ℕ

/-- Well-formedness of an instance: `X`, `Y` and the target vector all have `m` entries, and
every size and every target is positive. -/
def WellFormed (i : NumericalMatchingWithTargetSumsInstance) : Prop :=
  i.2.1.length = i.1.length ∧ i.2.2.length = i.1.length ∧
    (∀ a ∈ i.1, 0 < a) ∧ (∀ a ∈ i.2.1, 0 < a) ∧ ∀ b ∈ i.2.2, 0 < b

/-- Some permutations `σ`, `τ` of `Fin m` give sets `A_k = {x_{σ k}, y_{τ k}}` with
`s(x_{σ k}) + s(y_{τ k}) = B_k` for every `k`. -/
def NumericalMatchingWithTargetSumsFeasible
    (i : NumericalMatchingWithTargetSumsInstance) : Prop :=
  ∃ σ τ : Equiv.Perm (Fin i.1.length), ∀ k : Fin i.1.length,
    i.1.getD (σ k) 0 + i.2.1.getD (τ k) 0 = i.2.2.getD k 0

open Classical in
/-- NUMERICAL MATCHING WITH TARGET SUMS as a decision problem over bitstrings. -/
noncomputable def numericalMatchingWithTargetSumsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NumericalMatchingWithTargetSumsInstance) x with
  | some i => decide (WellFormed i ∧ NumericalMatchingWithTargetSumsFeasible i)
  | none => false

/-- **NUMERICAL MATCHING WITH TARGET SUMS is NP-complete.** Source: Garey and Johnson (1979),
[SP17]. -/
public theorem_wanted numericalMatchingWithTargetSums_npComplete :
    numericalMatchingWithTargetSumsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L numericalMatchingWithTargetSumsDec

end MetaMathlibExt.Complexity.NPComplete.NumericalMatchingWithTargetSums
