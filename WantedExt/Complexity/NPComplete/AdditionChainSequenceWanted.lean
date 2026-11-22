/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ADDITION CHAIN FOR A SEQUENCE is NP-complete

Source:
P. Downey, B. Leong and R. Sethi, "Computing sequences with addition chains", SIAM Journal on
Computing 10 (1981), 638-646, doi:10.1137/0210047.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AdditionChainSequence

/-!
# ADDITION CHAIN FOR A SEQUENCE is NP-complete

INSTANCE: a sequence `n₁, …, nₘ` (`m ≥ 1`) of positive integers and a positive integer `K`.
QUESTION: is there an addition chain `1 = a₀ < a₁ < ⋯ < a_r` with `r ≤ K` that contains every
`nᵢ`, where each `aᵢ` with `i ≥ 1` is `aⱼ + a_k` for some `j, k < i` (`j = k` allowed)?

Downey, Leong and Sethi (abstract) ask for the smallest number of additions needed to compute
all of `n₁, …, nₘ` starting with 1, call this generalization of the addition chain problem
(`m = 1`) the addition-sequence problem, and show that it is NP-complete. A chain
`a₀, …, a_r` uses `r` additions, so the decision form asks for a chain of length `r ≤ K`.
Chains are taken strictly increasing, as is usual for addition chains; this does not change
the question, since deleting repeated values from a chain and sorting the rest gives a chain
of no greater length containing the same numbers.

Numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the sequence `[n₁, …, nₘ]` and the bound `K`. -/
abbrev AdditionChainSequenceInstance := List ℕ × ℕ

/-- `a = [a₀, a₁, …, a_r]` is an addition chain: `a₀ = 1`, the entries strictly increase, and
every entry after the first is the sum of two (not necessarily distinct) earlier entries. -/
def IsAdditionChain (a : List ℕ) : Prop :=
  a.head? = some 1 ∧ a.Pairwise (· < ·) ∧
    ∀ i : Fin a.length, 0 < i.val →
      ∃ j k : Fin a.length, j < i ∧ k < i ∧ a[i] = a[j] + a[k]

/-- Well-formedness of an instance: the sequence is nonempty, its entries are positive, and the
bound `K` is positive. -/
def WellFormed (i : AdditionChainSequenceInstance) : Prop :=
  i.1 ≠ [] ∧ (∀ n ∈ i.1, 0 < n) ∧ 0 < i.2

/-- Some addition chain `a₀, …, a_r` with `r ≤ K` contains every number of the sequence. -/
def AdditionChainSequenceFeasible (i : AdditionChainSequenceInstance) : Prop :=
  ∃ a : List ℕ, IsAdditionChain a ∧ a.length ≤ i.2 + 1 ∧ ∀ n ∈ i.1, n ∈ a

open Classical in
/-- ADDITION CHAIN FOR A SEQUENCE as a decision problem over bitstrings. -/
noncomputable def additionChainSequenceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AdditionChainSequenceInstance) x with
  | some i => decide (WellFormed i ∧ AdditionChainSequenceFeasible i)
  | none => false

/-- **ADDITION CHAIN FOR A SEQUENCE is NP-complete.** Source: Downey, Leong and Sethi
(1981). -/
public theorem_wanted additionChainSequence_npComplete :
    additionChainSequenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L additionChainSequenceDec

end MetaMathlibExt.Complexity.NPComplete.AdditionChainSequence
