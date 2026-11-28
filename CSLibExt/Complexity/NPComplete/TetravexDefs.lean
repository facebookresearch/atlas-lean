/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

/-!
# TETRAVEX: definitions

INSTANCE: a side length `n` and `n²` unit square tiles, each edge of which is labelled with a
number. QUESTION: can each tile be placed within an
`n × n` square, every tile used exactly once and none rotated, such that all neighbouring
edges are labelled with an identical number?

A tile `(a, b, c, d)` has top label `a`, right label `b`, bottom label `c` and left label `d`.
Positions `(x, y)` with `x, y < n` count columns left to right and rows top to bottom. The
tiles form a list, so equal tiles may occur several times; each list entry is placed once.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
Y. Takenaga and T. Walsh, "Tetravex is NP-complete", Information Processing Letters 99 (2006),
171-174, doi:10.1016/j.ipl.2006.04.010 (arXiv:0903.1147).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Tetravex

/-- An instance: the side length `n` and the list of tiles; a tile `(a, b, c, d)` is labelled
top `a`, right `b`, bottom `c`, left `d`. -/
abbrev TetravexInstance := ℕ × List (ℕ × ℕ × ℕ × ℕ)

/-- Well-formedness of an instance: there are exactly `n²` tiles. -/
def WellFormed (i : TetravexInstance) : Prop :=
  i.2.length = i.1 * i.1

/-- A Tetravex solution: `f x y` is the index (in the tile list) of the tile placed at position
`(x, y)`. Every position gets a tile, distinct positions get distinct tiles (with `n²` tiles and
`n²` positions, every tile is placed exactly once), horizontally neighbouring tiles agree on
the right and left labels, and vertically neighbouring tiles agree on the bottom and top
labels. -/
def TetravexFeasible (i : TetravexInstance) : Prop :=
  ∃ f : ℕ → ℕ → ℕ,
    (∀ x < i.1, ∀ y < i.1, f x y < i.2.length) ∧
    (∀ x < i.1, ∀ y < i.1, ∀ x' < i.1, ∀ y' < i.1, f x y = f x' y' → x = x' ∧ y = y') ∧
    (∀ x y, x + 1 < i.1 → y < i.1 →
      (i.2.getD (f x y) (0, 0, 0, 0)).2.1 = (i.2.getD (f (x + 1) y) (0, 0, 0, 0)).2.2.2) ∧
    (∀ x y, x < i.1 → y + 1 < i.1 →
      (i.2.getD (f x y) (0, 0, 0, 0)).2.2.1 = (i.2.getD (f x (y + 1)) (0, 0, 0, 0)).1)

open Classical in
/-- TETRAVEX as a decision problem over bitstrings. -/
noncomputable def tetravexDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TetravexInstance) x with
  | some i => decide (WellFormed i ∧ TetravexFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Tetravex
