/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ADDITION CHAIN FOR A SEQUENCE: definitions

Source:
P. Downey, B. Leong and R. Sethi, "Computing sequences with addition chains", SIAM Journal on
Computing 10 (1981), 638-646, doi:10.1137/0210047.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AdditionChainSequence

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

end MetaMathlibExt.Complexity.NPComplete.AdditionChainSequence
