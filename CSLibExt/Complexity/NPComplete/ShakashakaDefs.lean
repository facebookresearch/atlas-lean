/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHAKASHAKA: definitions

Source:
E. D. Demaine, Y. Okamoto, R. Uehara and Y. Uno, "Computational complexity and an integer
programming model of Shakashaka", IEICE Transactions on Fundamentals of Electronics,
Communications and Computer Sciences E97-A(6) (2014), 1213-1219,
doi:10.1587/transfun.E97.A.1213 (conference version: 25th Canadian Conference on
Computational Geometry, CCCG 2013), Section 2 (definition) and Theorem 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Shakashaka

/-- An instance: the board as a list of `m` rows of `n` entries; `0` is a white square, `1` an
unnumbered black square, and `2 + i` a black square containing the number `i`. -/
abbrev ShakashakaInstance := List (List ℕ)

/-- The entry of square `(r, c)` (black, `1`, outside the board). -/
def cell (i : ShakashakaInstance) (r c : ℕ) : ℕ :=
  (i.getD r []).getD c 1

/-- Well-formedness: every row is as long as the first, and every entry is at most `6`
(numbers `0, …, 4`). -/
def WellFormed (i : ShakashakaInstance) : Prop :=
  (∀ row ∈ i, row.length = (i.getD 0 []).length) ∧ ∀ row ∈ i, ∀ x ∈ row, x ≤ 6

/-- The closed white part of square `(r, c)` under option `t`. With local coordinates
`u = x - r`, `v = y - c` in `[0, 1]`: option `0` leaves the square white; options `1, 2, 3, 4`
place the black half-square with its right angle at the corner `(r, c)`, `(r, c + 1)`,
`(r + 1, c)`, `(r + 1, c + 1)` respectively, leaving the opposite closed half white. -/
def whitePart (r c : ℕ) (t : Fin 5) : Set (ℝ × ℝ) :=
  {p | (r : ℝ) ≤ p.1 ∧ p.1 ≤ r + 1 ∧ (c : ℝ) ≤ p.2 ∧ p.2 ≤ c + 1 ∧
    match (t : ℕ) with
    | 0 => True
    | 1 => 1 ≤ (p.1 - r) + (p.2 - c)
    | 2 => p.2 - c ≤ p.1 - r
    | 3 => p.1 - r ≤ p.2 - c
    | _ => (p.1 - r) + (p.2 - c) ≤ 1}

/-- The union of the closed white parts of the white squares under the options `sol`. -/
def whiteSet (i : ShakashakaInstance) (sol : ℕ → ℕ → Fin 5) : Set (ℝ × ℝ) :=
  {p | ∃ r < i.length, ∃ c < (i.getD 0 []).length, cell i r c = 0 ∧ p ∈ whitePart r c (sol r c)}

/-- The instance has a solution: options `sol` for the white squares (entries of `sol` at other
squares are ignored) such that every numbered black square has exactly its number of b/w squares
among its four neighbors, and every connected component of the white area is an open
axis-parallel or `45°` rectangle. -/
def ShakashakaFeasible (i : ShakashakaInstance) : Prop :=
  ∃ sol : ℕ → ℕ → Fin 5,
    (∀ r < i.length, ∀ c < (i.getD 0 []).length, 2 ≤ cell i r c →
      ((Finset.range i.length ×ˢ Finset.range (i.getD 0 []).length).filter fun q =>
          (q.1 + 1 = r ∧ q.2 = c ∨ q.1 = r + 1 ∧ q.2 = c ∨
            q.1 = r ∧ q.2 + 1 = c ∨ q.1 = r ∧ q.2 = c + 1) ∧
          cell i q.1 q.2 = 0 ∧ sol q.1 q.2 ≠ 0).card = cell i r c - 2) ∧
    ∀ p ∈ interior (whiteSet i sol), ∃ a₁ a₂ b₁ b₂ : ℝ,
      connectedComponentIn (interior (whiteSet i sol)) p =
          {q | a₁ < q.1 ∧ q.1 < a₂ ∧ b₁ < q.2 ∧ q.2 < b₂} ∨
        connectedComponentIn (interior (whiteSet i sol)) p =
          {q | a₁ < q.1 + q.2 ∧ q.1 + q.2 < a₂ ∧ b₁ < q.1 - q.2 ∧ q.1 - q.2 < b₂}

open Classical in
/-- SHAKASHAKA as a decision problem over bitstrings. -/
noncomputable def shakashakaDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShakashakaInstance) x with
  | some i => decide (WellFormed i ∧ ShakashakaFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Shakashaka
