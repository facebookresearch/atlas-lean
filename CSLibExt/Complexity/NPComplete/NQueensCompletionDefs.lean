/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# N-QUEENS COMPLETION: definitions

Source:
I. P. Gent, C. Jefferson and P. Nightingale, "Complexity of n-Queens Completion",
Journal of Artificial Intelligence Research 59 (2017), 815-848, doi:10.1613/jair.5512
(Problem 2; Theorem 37).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NQueensCompletion

/-- An instance: the board row by row, `true` for a placed queen. -/
abbrev NQueensCompletionInstance := List (List Bool)

/-- The board size `n` (the number of rows). -/
def size (i : NQueensCompletionInstance) : ℕ := i.length

/-- The queen `(α, β)` (column `α`, row `β`) is placed: entry `α` of row `β` is `true`. -/
def Placed (i : NQueensCompletionInstance) (q : ℕ × ℕ) : Prop :=
  (i.getD q.2 []).getD q.1 false = true

/-- Queen `q` attacks queen `q'`: they are not equal and share a column, a row, a
sum-diagonal, or a difference-diagonal. -/
def Attacks (q q' : ℕ × ℕ) : Prop :=
  q ≠ q' ∧ (q.1 = q'.1 ∨ q.2 = q'.2 ∨ q.1 + q.2 = q'.1 + q'.2 ∨
    (q.1 : ℤ) - q.2 = (q'.1 : ℤ) - q'.2)

/-- Well-formedness: `n ≥ 1`, the board is `n × n`, and no two placed queens share a row or a
column. -/
def WellFormed (i : NQueensCompletionInstance) : Prop :=
  1 ≤ size i ∧ (∀ row ∈ i, row.length = size i) ∧
    (∀ β < size i, ∀ α < size i, ∀ α' < size i, Placed i (α, β) → Placed i (α', β) → α = α') ∧
    ∀ α < size i, ∀ β < size i, ∀ β' < size i, Placed i (α, β) → Placed i (α, β') → β = β'

/-- Some solution `S` to `n`-Queens (`n` queens on board size `n`, no two attacking) contains
every placed queen. -/
def NQueensCompletionFeasible (i : NQueensCompletionInstance) : Prop :=
  ∃ S : Finset (ℕ × ℕ), (∀ q ∈ S, q.1 < size i ∧ q.2 < size i) ∧ S.card = size i ∧
    (∀ q ∈ S, ∀ q' ∈ S, ¬ Attacks q q') ∧
    ∀ α < size i, ∀ β < size i, Placed i (α, β) → (α, β) ∈ S

open Classical in
/-- N-QUEENS COMPLETION as a decision problem over bitstrings. -/
noncomputable def nQueensCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NQueensCompletionInstance) x with
  | some i => decide (WellFormed i ∧ NQueensCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NQueensCompletion
