/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SNAKE CUBE: definitions

Source:
Z. Abel, E. D. Demaine, M. L. Demaine, S. Eisenstat, J. Lynch and T. B. Schardl,
"Finding a Hamiltonian path in a cube with specified turns is hard", Journal of
Information Processing 21(3) (2013), 368-377, doi:10.2197/ipsjjip.21.368.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SnakeCube

/-- An instance: the side length `N` and the puzzle, a list of symbols, `false` for a straight
cube (S) and `true` for a turn cube (T). -/
abbrev SnakeCubeInstance := ℕ × List Bool

/-- A cell of the `N × N × N` cube, as its coordinate vector. -/
abbrev Cell (N : ℕ) := Fin 3 → Fin N

/-- The opposite face of a cell: same axis, other sign. -/
def opp (f : Fin 3 × Bool) : Fin 3 × Bool := (f.1, !f.2)

/-- `y` is the cell across the face of `x` with outward normal `f = (a, s)`: coordinate `a`
grows by one if `s = true` and shrinks by one if `s = false`; the other coordinates agree. -/
def Across {N : ℕ} (x : Cell N) (f : Fin 3 × Bool) (y : Cell N) : Prop :=
  (if f.2 then (y f.1 : ℕ) = x f.1 + 1 else (x f.1 : ℕ) = y f.1 + 1) ∧
    ∀ b, b ≠ f.1 → y b = x b

/-- Well-formedness: the side length `N` is positive and the puzzle has exactly `N³` symbols. -/
def WellFormed (i : SnakeCubeInstance) : Prop :=
  0 < i.1 ∧ i.2.length = i.1 ^ 3

/-- A folded state in the shape of the `N × N × N` cube: cells `c k`, pairwise distinct and
covering the cube (`c` is a bijection onto the cube's cells), with entry and exit faces `e k`,
`o k` such that consecutive cells share face `f_{k+1}`, and each cell is straight or turning
as its symbol says. -/
def SnakeCubeFeasible (i : SnakeCubeInstance) : Prop :=
  ∃ c : Fin (i.1 ^ 3) → Cell i.1, ∃ e o : Fin (i.1 ^ 3) → Fin 3 × Bool,
    Function.Bijective c ∧
    (∀ k : Fin (i.1 ^ 3), ∀ h : k.1 + 1 < i.1 ^ 3,
      Across (c k) (o k) (c ⟨k.1 + 1, h⟩) ∧ e ⟨k.1 + 1, h⟩ = opp (o k)) ∧
    ∀ k : Fin (i.1 ^ 3), if i.2.getD k.1 false then (e k).1 ≠ (o k).1 else e k = opp (o k)

open Classical in
/-- SNAKE CUBE as a decision problem over bitstrings. -/
noncomputable def snakeCubeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SnakeCubeInstance) x with
  | some i => decide (WellFormed i ∧ SnakeCubeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SnakeCube
