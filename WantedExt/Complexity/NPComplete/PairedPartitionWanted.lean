/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION choosing one element of each pair is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP12] PARTITION, comment ("Remains
NP-complete even if we require that `|A'| = |A|/2`, or if the elements in `A` are ordered as
`a₁, a₂, ..., a₂ₙ` and we require that `A'` contain exactly one of `a₂ᵢ₋₁, a₂ᵢ` for
`1 ≤ i ≤ n`"); the entry's reference is "[Karp, 1972]. Transformation from 3DM (see
Section 3.1.5)"; R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of
Computer Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PairedPartition

/-!
# PARTITION choosing one element of each pair is NP-complete

INSTANCE: a finite set `A = {a₁, a₂, ..., a₂ₙ}` and a size `s(a) ∈ ℤ⁺` for each `a ∈ A`.
QUESTION: is there a subset `A' ⊆ A` containing exactly one of `a₂ᵢ₋₁, a₂ᵢ` for `1 ≤ i ≤ n`
such that `∑_{a ∈ A'} s(a) = ∑_{a ∈ A - A'} s(a)`?

The instance is the list of the `n` pairs `(s(a₂ᵢ₋₁), s(a₂ᵢ))`. A subset `A'` containing exactly
one element of each pair is a list of `n` choices (`true` picks `a₂ᵢ₋₁`, `false` picks `a₂ᵢ`); the
two sums are equal exactly when the sum over `A'` is half the total.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the pairs `[(s(a₁), s(a₂)), ..., (s(a₂ₙ₋₁), s(a₂ₙ))]`. -/
abbrev PairedPartitionInstance := List (ℕ × ℕ)

/-- Well-formedness of an instance: every size is positive. -/
def WellFormed (i : PairedPartitionInstance) : Prop :=
  ∀ p ∈ i, 0 < p.1 ∧ 0 < p.2

/-- The size of the element chosen from a pair: the first if `b`, the second otherwise. -/
def chosen (p : ℕ × ℕ) (b : Bool) : ℕ :=
  if b then p.1 else p.2

/-- One element chosen from each pair, with the chosen sizes summing to half the total. -/
def PairedPartitionFeasible (i : PairedPartitionInstance) : Prop :=
  ∃ c : List Bool, c.length = i.length ∧
    (List.zipWith chosen i c).sum * 2 = (i.map fun p => p.1 + p.2).sum

open Classical in
/-- PARTITION choosing one element of each pair as a decision problem over bitstrings. -/
noncomputable def pairedPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PairedPartitionInstance) x with
  | some i => decide (WellFormed i ∧ PairedPartitionFeasible i)
  | none => false

/-- **PARTITION choosing one element of each pair is NP-complete.** Source: Garey and Johnson (1979), [SP12], comment. -/
public theorem_wanted pairedPartition_npComplete :
    pairedPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pairedPartitionDec

end MetaMathlibExt.Complexity.NPComplete.PairedPartition
