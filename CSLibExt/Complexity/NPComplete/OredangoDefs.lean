/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OREDANGO: definitions

Source:
T. Takahata, N. Minamikawa and T. Okuno, "Computational complexity and integer programming
formulation of the Oredango puzzle", arXiv:2503.10393 (2025) (Section 1, rules (a)-(d) and
Theorem 1.1).
-/
module

public import Batteries.Data.List.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Oredango

/-- An instance: the numbers `m` of rows and `n` of columns, and the skewers, each its circles in
order, a flag saying whether it holds an integer, and that integer. -/
abbrev OredangoInstance := ℕ × ℕ × List (List (ℕ × ℕ) × Bool × ℕ)

/-- The circles of the instance: the cells of all skewers. -/
def circles (i : OredangoInstance) : List (ℕ × ℕ) :=
  i.2.2.flatMap (·.1)

/-- Two cells share a side. -/
def SideAdjacent (a b : ℕ × ℕ) : Prop :=
  (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)) ∨ (a.2 = b.2 ∧ (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1))

/-- Well-formedness of an instance: the grid has at least one row and one column, every skewer
is nonempty and joins side-adjacent cells in order, every circle is a cell of the grid, and no
cell holds two circles (so every circle is on exactly one skewer). -/
def WellFormed (i : OredangoInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ (∀ s ∈ i.2.2, s.1 ≠ [] ∧ s.1.IsChain SideAdjacent) ∧
    (∀ c ∈ circles i, c.1 < i.1 ∧ c.2 < i.2.1) ∧ (circles i).Nodup

/-- `a`, `b`, `c` are three consecutive circles of a row: same row, increasing columns, and no
circle of that row strictly between `a` and `b` or between `b` and `c`. -/
def RowConsecutive (i : OredangoInstance) (a b c : ℕ × ℕ) : Prop :=
  a ∈ circles i ∧ b ∈ circles i ∧ c ∈ circles i ∧ a.1 = b.1 ∧ b.1 = c.1 ∧ a.2 < b.2 ∧
    b.2 < c.2 ∧ ∀ d ∈ circles i, d.1 = a.1 → ¬ (a.2 < d.2 ∧ d.2 < b.2) ∧ ¬ (b.2 < d.2 ∧ d.2 < c.2)

/-- `a`, `b`, `c` are three consecutive circles of a column: same column, increasing rows, and
no circle of that column strictly between `a` and `b` or between `b` and `c`. -/
def ColumnConsecutive (i : OredangoInstance) (a b c : ℕ × ℕ) : Prop :=
  a ∈ circles i ∧ b ∈ circles i ∧ c ∈ circles i ∧ a.2 = b.2 ∧ b.2 = c.2 ∧ a.1 < b.1 ∧
    b.1 < c.1 ∧ ∀ d ∈ circles i, d.2 = a.2 → ¬ (a.1 < d.1 ∧ d.1 < b.1) ∧ ¬ (b.1 < d.1 ∧ d.1 < c.1)

/-- Some coloring satisfies rules (a)-(d). -/
def OredangoFeasible (i : OredangoInstance) : Prop :=
  ∃ black : ℕ × ℕ → Bool,
    (∀ s ∈ i.2.2, s.2.1 = true → (s.1.filter black).length = s.2.2) ∧
    (∀ s ∈ i.2.2, ∀ k, (h : k + 2 < s.1.length) →
      ¬ (black s.1[k] = black s.1[k + 1] ∧ black s.1[k + 1] = black s.1[k + 2])) ∧
    (∀ a b c, RowConsecutive i a b c → ¬ (black a = black b ∧ black b = black c)) ∧
    ∀ a b c, ColumnConsecutive i a b c → ¬ (black a = black b ∧ black b = black c)

open Classical in
/-- OREDANGO as a decision problem over bitstrings. -/
noncomputable def oredangoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OredangoInstance) x with
  | some i => decide (WellFormed i ∧ OredangoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Oredango
