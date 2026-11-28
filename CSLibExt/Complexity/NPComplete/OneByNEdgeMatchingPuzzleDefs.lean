/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 1 × n EDGE-MATCHING PUZZLE: definitions

Source:
J. Bosboom, E. D. Demaine, M. L. Demaine, A. Hesterberg, P. Manurangsi, and A. Yodpinyanee,
"Even 1 × n edge-matching and jigsaw puzzles are really hard", Journal of Information
Processing 25 (2017), 682-694, doi:10.2197/ipsjjip.25.682 (arXiv:1701.00146), Definition 3
(`h × w` Edge-Matching Puzzle) and Theorem 1 (gap hardness of 1 × n placement, whose yes side
is a complete assembly);
M. Ebbesen, P. Fischer, and C. Witt, "Edge-matching problems with rotations", in *Fundamentals of
Computation Theory (FCT 2011)*, Lecture Notes in Computer Science 6914 (2011), 114-125,
doi:10.1007/978-3-642-22953-4_10 (NP-hardness for a `1 × n` target, as cited by Bosboom et al.).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.EdgeMatchingPuzzleDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OneByNEdgeMatchingPuzzle

/-- An instance: the tiles `(top, right, bottom, left)`. -/
abbrev OneByNEdgeMatchingPuzzleInstance := List (ℕ × ℕ × ℕ × ℕ)

/-- The edge-matching instance on the `1 × n` board, `n` the number of tiles. -/
def strip (i : OneByNEdgeMatchingPuzzleInstance) : EdgeMatchingPuzzle.EdgeMatchingPuzzleInstance :=
  (i, 1, i.length)

/-- Well-formedness of an instance: there is at least one tile. -/
def WellFormed (i : OneByNEdgeMatchingPuzzleInstance) : Prop :=
  i ≠ []

open Classical in
/-- 1 × n EDGE-MATCHING PUZZLE as a decision problem over bitstrings: the edge-matching puzzle
on the `1 × n` board. -/
noncomputable def oneByNEdgeMatchingPuzzleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OneByNEdgeMatchingPuzzleInstance) x with
  | some i => decide (WellFormed i ∧ EdgeMatchingPuzzle.EdgeMatchingPuzzleFeasible (strip i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OneByNEdgeMatchingPuzzle
