/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HEYAWAKE: definitions

Source:
M. Holzer and O. Ruepp, "The troubles of interior design: a complexity analysis of the game
Heyawake", Fun with Algorithms (FUN 2007), Lecture Notes in Computer Science 4475 (2007),
198-212, doi:10.1007/978-3-540-72914-3_18.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Finset.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Heyawake

/-- An instance: the grid row by row (the room index of each cell), and for each room whether
it is numbered and its number. -/
abbrev HeyawakeInstance := List (List ℕ) × List (Bool × ℕ)

/-- The number of rows. -/
def rows (i : HeyawakeInstance) : ℕ := i.1.length

/-- The number of columns (the length of the first row). -/
def cols (i : HeyawakeInstance) : ℕ := (i.1.headD []).length

/-- The room of cell `(r, c)`. -/
def roomOf (i : HeyawakeInstance) (r c : ℕ) : ℕ := (i.1.getD r []).getD c 0

/-- Well-formedness: at least one row and one column, rows of equal length, room indices in
range, every room nonempty, and every room rectangular (it contains the bounding box of any two
of its cells). -/
def WellFormed (i : HeyawakeInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.1, row.length = cols i) ∧
    (∀ row ∈ i.1, ∀ k ∈ row, k < i.2.length) ∧
    (∀ k < i.2.length, ∃ r < rows i, ∃ c < cols i, roomOf i r c = k) ∧
    ∀ r₁ < rows i, ∀ c₁ < cols i, ∀ r₂ < rows i, ∀ c₂ < cols i,
      roomOf i r₁ c₁ = roomOf i r₂ c₂ →
      ∀ r < rows i, ∀ c < cols i, min r₁ r₂ ≤ r → r ≤ max r₁ r₂ → min c₁ c₂ ≤ c →
        c ≤ max c₁ c₂ → roomOf i r c = roomOf i r₁ c₁

/-- The grid graph on `Fin m × Fin n`: cells sharing a side are adjacent. -/
def gridGraph (m n : ℕ) : SimpleGraph (Fin m × Fin n) :=
  SimpleGraph.pathGraph m □ SimpleGraph.pathGraph n

/-- The painting `p` (`true` = painted) satisfies the four rules. -/
def Solves (i : HeyawakeInstance) (p : ℕ → ℕ → Bool) : Prop :=
  -- 1. painted cells are never orthogonally adjacent
  (∀ r < rows i, ∀ c < cols i, p r c = true →
    (r + 1 < rows i → p (r + 1) c = false) ∧ (c + 1 < cols i → p r (c + 1) = false)) ∧
  -- 2. the white cells are interconnected (they form a single nonempty region)
  ((gridGraph (rows i) (cols i)).induce {x | p x.1 x.2 = false}).Connected ∧
  -- 3. a numbered room contains exactly that many painted cells
  (∀ k < i.2.length, (i.2.getD k (false, 0)).1 = true →
    ((Finset.range (rows i) ×ˢ Finset.range (cols i)).filter
      fun x => roomOf i x.1 x.2 = k ∧ p x.1 x.2 = true).card = (i.2.getD k (false, 0)).2) ∧
  -- 4. no straight line of consecutive white cells meets more than two rooms
  (∀ r < rows i, ∀ c₁ c₂ c₃, c₁ < c₂ → c₂ < c₃ → c₃ < cols i →
    (∀ c, c₁ ≤ c → c ≤ c₃ → p r c = false) →
      roomOf i r c₁ = roomOf i r c₂ ∨ roomOf i r c₁ = roomOf i r c₃ ∨
        roomOf i r c₂ = roomOf i r c₃) ∧
  (∀ c < cols i, ∀ r₁ r₂ r₃, r₁ < r₂ → r₂ < r₃ → r₃ < rows i →
    (∀ r, r₁ ≤ r → r ≤ r₃ → p r c = false) →
      roomOf i r₁ c = roomOf i r₂ c ∨ roomOf i r₁ c = roomOf i r₃ c ∨
        roomOf i r₂ c = roomOf i r₃ c)

/-- Some painting satisfies the rules. -/
def HeyawakeFeasible (i : HeyawakeInstance) : Prop :=
  ∃ p : ℕ → ℕ → Bool, Solves i p

open Classical in
/-- HEYAWAKE as a decision problem over bitstrings. -/
noncomputable def heyawakeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HeyawakeInstance) x with
  | some i => decide (WellFormed i ∧ HeyawakeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Heyawake
