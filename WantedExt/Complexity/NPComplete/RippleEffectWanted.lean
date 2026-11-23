/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RIPPLE EFFECT is NP-complete

Source:
Y. Takenaga, S. Aoyagi, S. Iwata and T. Kasai, "Shikaku and ripple effect are NP-complete",
Congressus Numerantium 216 (2013), 119-127, MR3220078;
puzzle rules: Nikoli Co., Ltd., "Ripple Effect", https://www.nikoli.co.jp/en/puzzles/ripple_effect/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RippleEffect

/-!
# RIPPLE EFFECT is NP-complete

Ripple Effect (Nikoli) is played on a rectangular grid divided by bold lines into areas called
rooms; some cells contain numbers. Nikoli's rules: "The areas divided by bold lines are called
'Rooms'. Fill in all empty cells with numbers under the following rules. Each Room contains
consecutive numbers starting from 1. If a number is duplicated in a row or a column, the space
between the duplicated numbers must be equal to or larger than the value of the number."
Takenaga, Aoyagi, Iwata and Kasai (2013) prove that deciding whether a Ripple Effect instance
has a solution is NP-complete.

INSTANCE: an `m × n` grid divided into connected rooms, some cells containing numbers.
QUESTION: can the empty cells be filled so that a room of `k` cells holds the numbers
`1, …, k`, and any two cells of one row or column holding the same number `d` have at least
`d` cells between them?

Representation. The grid is given row by row; a cell is a pair `(k, g)` of its room label `k`
and its number `g` (`0` for an empty cell), so the instance size is proportional to the area
plus the binary length of the entries. A room is the set of cells with one label; `WellFormed`
requires every room to be connected (`SimpleGraph.Preconnected` of the subgraph that Mathlib's
grid graph `pathGraph m □ pathGraph n` induces on it). A filling is a function `ℕ → ℕ → ℕ` read
on the grid that keeps the given numbers. "Consecutive numbers starting from 1" in a room of
`k` cells means the numbers `1, …, k`, each once: every number lies in `[1, k]` and no number
repeats in the room. Cells `(r, c)` and `(r, c')`, `c < c'`, have `c' - c - 1` cells between
them, so the spacing rule reads `c + d < c'`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **RIPPLE EFFECT is NP-complete.** Source: Takenaga, Aoyagi, Iwata and Kasai (2013). -/
public theorem_wanted rippleEffect_npComplete :
    rippleEffectDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rippleEffectDec

end MetaMathlibExt.Complexity.NPComplete.RippleEffect
