/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NAGARERU: definitions

Source:
C. Iwamoto and T. Ide, "Moon-or-Sun, Nagareru, and Nurimeizu are NP-complete",
IEICE Transactions on Fundamentals of Electronics, Communications and Computer Sciences
E105-A(9) (2022), 1187-1194, doi:10.1587/transfun.2021DMP0006;
puzzle rules: Nikoli Co., Ltd., "Nagareru" (流れるループ),
https://www.nikoli.co.jp/en/puzzles/nagareru/ and https://www.nikoli.co.jp/ja/puzzles/nagareru/.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nagareru

/-- An instance: the grid row by row, each cell coded `0` (white), `1 + a` (white, arrow `a`),
`5` (black) or `6 + a` (black, arrow `a`). -/
abbrev NagareruInstance := List (List ℕ)

/-- The number of rows. -/
def rows (i : NagareruInstance) : ℕ := i.length

/-- The number of columns (the length of the first row). -/
def cols (i : NagareruInstance) : ℕ := (i.headD []).length

/-- The code of cell `x`. -/
def entry (i : NagareruInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ :=
  (i.getD x.1 []).getD x.2 0

/-- Well-formedness: at least one row and one column, rows of equal length, codes at most `9`. -/
def WellFormed (i : NagareruInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧ ∀ row ∈ i, ∀ e ∈ row, e ≤ 9

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : NagareruInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- `y` is the neighbour of `x` in direction `w` (`0` up, `1` right, `2` down, `3` left). -/
def Step {m n : ℕ} (x y : Fin m × Fin n) : ℕ → Prop
  | 0 => y.2 = x.2 ∧ y.1.val + 1 = x.1.val
  | 1 => y.1 = x.1 ∧ y.2.val = x.2.val + 1
  | 2 => y.2 = x.2 ∧ y.1.val = x.1.val + 1
  | _ => y.1 = x.1 ∧ y.2.val + 1 = x.2.val

/-- `y` lies strictly beyond `b` in direction `w`, in the same row or column. -/
def Beyond {m n : ℕ} (b y : Fin m × Fin n) : ℕ → Prop
  | 0 => y.2 = b.2 ∧ y.1 < b.1
  | 1 => y.1 = b.1 ∧ b.2 < y.2
  | 2 => y.2 = b.2 ∧ b.1 < y.1
  | _ => y.1 = b.1 ∧ y.2 < b.2

/-- Wind with direction `w` blows in cell `x`: some black cell `b` with arrow `w` has `x` beyond
it in direction `w`, and no cell after `b` up to and including `x` is black. -/
def Windy (i : NagareruInstance) (x : Fin (rows i) × Fin (cols i)) (w : ℕ) : Prop :=
  ∃ b, entry i b = 6 + w ∧ Beyond b x w ∧
    ∀ y, Beyond b y w → (Beyond y x w ∨ y = x) → entry i y < 5

/-- The directed cycle `c` satisfies rules 1-4. -/
def Solves (i : NagareruInstance) {u : Fin (rows i) × Fin (cols i)}
    (c : (Grid i).Walk u u) : Prop :=
  -- 1. the loop passes only through white cells
  (∀ x ∈ c.support, entry i x < 5) ∧
  -- 2. it passes every white arrow cell, moving into and out of it along the arrow
  (∀ x, 1 ≤ entry i x → entry i x ≤ 4 → x ∈ c.support) ∧
  (∀ d ∈ c.darts, ∀ a < 4, (entry i d.fst = 1 + a ∨ entry i d.snd = 1 + a) →
    Step d.fst d.snd a) ∧
  -- 3. no move into or out of a windy cell goes against the wind
  (∀ d ∈ c.darts, ∀ w < 4, (Windy i d.fst w ∨ Windy i d.snd w) →
    ¬ Step d.fst d.snd ((w + 2) % 4)) ∧
  -- 4. entering a windy cell from the side, the loop next moves downwind
  ∀ d ∈ c.darts, ∀ d' ∈ c.darts, d.snd = d'.fst → ∀ w < 4, Windy i d.snd w →
    (Step d.fst d.snd ((w + 1) % 4) ∨ Step d.fst d.snd ((w + 3) % 4)) →
      Step d'.fst d'.snd w

/-- Some directed cycle of the grid graph satisfies the rules. -/
def NagareruFeasible (i : NagareruInstance) : Prop :=
  ∃ u, ∃ c : (Grid i).Walk u u, c.IsCycle ∧ Solves i c

open Classical in
/-- NAGARERU as a decision problem over bitstrings. -/
noncomputable def nagareruDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NagareruInstance) x with
  | some i => decide (WellFormed i ∧ NagareruFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Nagareru
