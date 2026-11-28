/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EYE-WITLESS: definitions

Source:
H. Tang, "On the NP-completeness of satisfying certain path and loop puzzles",
arXiv:2004.12849 (2020), Sections 1.1 and 3.1;
puzzle rules: TheGreatEscaper, "The Ludicrous Loop: over a thousand cells of circular logic",
https://puzzling.stackexchange.com/q/52899/ (2017).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EyeWitless

/-- An instance: the grid row by row, `0` for a cell without an eye and `k + 1` for an eye of
colour `k`. -/
abbrev EyeWitlessInstance := List (List ℕ)

/-- The number of rows `m`. -/
def rows (i : EyeWitlessInstance) : ℕ := i.length

/-- The number of columns `n` (the length of the first row). -/
def cols (i : EyeWitlessInstance) : ℕ := (i.headD []).length

/-- The entry of cell `x`: `0` without an eye, `k + 1` for an eye of colour `k`. -/
def eye (i : EyeWitlessInstance) (x : ℕ × ℕ) : ℕ := (i.getD x.1 []).getD x.2 0

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : EyeWitlessInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The edges of a walk, with cells as pairs of naturals. -/
def edgesOf (i : EyeWitlessInstance) {u v : Fin (rows i) × Fin (cols i)}
    (w : (Grid i).Walk u v) : List (Sym2 (ℕ × ℕ)) :=
  w.edges.map (Sym2.map fun p => ((p.1 : ℕ), (p.2 : ℕ)))

/-- The cell at distance `t` from `x` in direction `d`, if it has natural coordinates. -/
def shift (x : ℕ × ℕ) (d t : ℕ) : Option (ℕ × ℕ) :=
  if d = 0 then (if t ≤ x.1 then some (x.1 - t, x.2) else none)
  else if d = 1 then some (x.1, x.2 + t)
  else if d = 2 then some (x.1 + t, x.2)
  else if t ≤ x.2 then some (x.1, x.2 - t) else none

/-- The edge from the cell at distance `t` to the cell at distance `t + 1` from `x` in direction
`d` is one of the edges `E`. -/
def straightEdge (E : List (Sym2 (ℕ × ℕ))) (x : ℕ × ℕ) (d t : ℕ) : Bool :=
  match shift x d t, shift x d (t + 1) with
  | some p, some q => decide (s(p, q) ∈ E)
  | _, _ => false

/-- The arm of the loop with edges `E` from `x` in direction `d`: the number of consecutive edges
going straight from `x` that way (at most `b`). -/
def arm (E : List (Sym2 (ℕ × ℕ))) (x : ℕ × ℕ) (b d : ℕ) : ℕ :=
  ((List.range b).takeWhile fun t => straightEdge E x d t).length

/-- What the eye at `x` sees on the loop `l`: its arms up, right, down and left. -/
def view (i : EyeWitlessInstance) {u : Fin (rows i) × Fin (cols i)} (l : (Grid i).Walk u u)
    (x : ℕ × ℕ) : List ℕ :=
  [0, 1, 2, 3].map (arm (edgesOf i l) x (rows i + cols i))

/-- Well-formedness: at least one row and one column, and rows of equal length. -/
def WellFormed (i : EyeWitlessInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ ∀ row ∈ i, row.length = cols i

/-- Some loop passes every eye, and any two eyes of the same colour see the same thing up to a
rotation. -/
def EyeWitlessFeasible (i : EyeWitlessInstance) : Prop :=
  ∃ u : Fin (rows i) × Fin (cols i), ∃ l : (Grid i).Walk u u, l.IsCycle ∧
    (∀ x : Fin (rows i) × Fin (cols i), eye i (x.1, x.2) ≠ 0 → x ∈ l.support) ∧
    ∀ x y : Fin (rows i) × Fin (cols i), eye i (x.1, x.2) ≠ 0 →
      eye i (x.1, x.2) = eye i (y.1, y.2) →
        ∃ r < 4, view i l (x.1, x.2) = (view i l (y.1, y.2)).rotate r

open Classical in
/-- EYE-WITLESS as a decision problem over bitstrings. -/
noncomputable def eyeWitlessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EyeWitlessInstance) x with
  | some i => decide (WellFormed i ∧ EyeWitlessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EyeWitless
