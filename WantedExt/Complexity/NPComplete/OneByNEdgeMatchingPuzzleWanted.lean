/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 1 × n EDGE-MATCHING PUZZLE is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.EdgeMatchingPuzzleWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OneByNEdgeMatchingPuzzle

/-!
# 1 × n EDGE-MATCHING PUZZLE is NP-complete

INSTANCE: `n ≥ 1` unit-square tiles where each of the four sides has a color. QUESTION: can the
tiles be assembled into the `1 × n` rectangular grid so that any two adjacent pieces have the
same color on the shared edge? Tiles may be rotated but not reflected (Bosboom et al.,
Definition 3; without rotations the `1 × n` problem is polynomial).

This is `EdgeMatchingPuzzleWanted` (Demaine and Demaine's edge-matching puzzle on an `h × w`
rectangle) with `h = 1` and `w = n`: its tiles `(top, right, bottom, left)`, quarter-turn
rotations, bijective placement and matching condition are reused, and as in Definition 3 only
shared edges are constrained (the outer boundary is free).

Bosboom et al. prove that even distinguishing assemblies of all `n` tiles from placements of at
most `(1 - α) n` tiles is NP-hard (Theorem 1), so in particular deciding whether all tiles can be
assembled is NP-hard; they credit the first proof, for "a target shape of a 1 × n rectangle", to
Ebbesen, Fischer and Witt (2011). The placement and the rotations are a certificate, so the
problem is in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **1 × n EDGE-MATCHING PUZZLE is NP-complete.** Source: Bosboom, Demaine, Demaine,
Hesterberg, Manurangsi, and Yodpinyanee (2017), Definition 3 and Theorem 1; Ebbesen, Fischer,
and Witt (2011). -/
public theorem_wanted oneByNEdgeMatchingPuzzle_npComplete :
    oneByNEdgeMatchingPuzzleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L oneByNEdgeMatchingPuzzleDec

end MetaMathlibExt.Complexity.NPComplete.OneByNEdgeMatchingPuzzle
