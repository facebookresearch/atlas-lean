/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RIPPLE EFFECT: definitions

Source:
Y. Takenaga, S. Aoyagi, S. Iwata and T. Kasai, "Shikaku and ripple effect are NP-complete",
Congressus Numerantium 216 (2013), 119-127, MR3220078;
puzzle rules: Nikoli Co., Ltd., "Ripple Effect", https://www.nikoli.co.jp/en/puzzles/ripple_effect/.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RippleEffect

/-- An instance: the grid row by row, each cell a pair `(room label, given number)` with `0`
for an empty cell. -/
abbrev RippleEffectInstance := List (List (ℕ × ℕ))

/-- The number of rows `m`. -/
def rows (i : RippleEffectInstance) : ℕ := i.length

/-- The number of columns `n` (the length of the first row). -/
def cols (i : RippleEffectInstance) : ℕ := (i.headD []).length

/-- The room label of cell `x`. -/
def room (i : RippleEffectInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ :=
  ((i.getD x.1 []).getD x.2 (0, 0)).1

/-- The number given in cell `x` (`0` if empty). -/
def given (i : RippleEffectInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ :=
  ((i.getD x.1 []).getD x.2 (0, 0)).2

/-- The number of cells in the room of cell `x`. -/
def roomSize (i : RippleEffectInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ :=
  (Finset.univ.filter fun y => room i y = room i x).card

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : RippleEffectInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, and every room
connected. -/
def WellFormed (i : RippleEffectInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    ∀ k, ((Grid i).induce {x | room i x = k}).Preconnected

/-- Some filling `f` keeps the given numbers, fills every room of `k` cells with `1, …, k`, and
separates equal numbers `d` in a row or a column by at least `d` cells. -/
def RippleEffectFeasible (i : RippleEffectInstance) : Prop :=
  ∃ f : ℕ → ℕ → ℕ,
    (∀ x : Fin (rows i) × Fin (cols i), given i x ≠ 0 → f x.1 x.2 = given i x) ∧
    (∀ x : Fin (rows i) × Fin (cols i), 1 ≤ f x.1 x.2 ∧ f x.1 x.2 ≤ roomSize i x) ∧
    (∀ x y : Fin (rows i) × Fin (cols i), room i x = room i y → f x.1 x.2 = f y.1 y.2 →
      x = y) ∧
    (∀ x y : Fin (rows i) × Fin (cols i), x.1 = y.1 → x.2 < y.2 → f x.1 x.2 = f y.1 y.2 →
      (x.2 : ℕ) + f x.1 x.2 < y.2) ∧
    (∀ x y : Fin (rows i) × Fin (cols i), x.2 = y.2 → x.1 < y.1 → f x.1 x.2 = f y.1 y.2 →
      (x.1 : ℕ) + f x.1 x.2 < y.1)

open Classical in
/-- RIPPLE EFFECT as a decision problem over bitstrings. -/
noncomputable def rippleEffectDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RippleEffectInstance) x with
  | some i => decide (WellFormed i ∧ RippleEffectFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RippleEffect
