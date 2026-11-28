/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NUMBERLINK with obstacles (vertex-disjoint paths in grid graphs) is NP-complete

Source:
J. F. Lynch, "The equivalence of theorem proving and the interconnection problem", ACM SIGDA
Newsletter 5(3) (1975), 31-36, doi:10.1145/1061425.1061430;
A. Adcock, E. D. Demaine, M. L. Demaine, M. P. O'Brien, F. Reidl, F. Sánchez Villaamil, and
B. D. Sullivan, "Zig-zag Numberlink is NP-complete", Journal of Information Processing 23(3)
(2015), 239-245, doi:10.2197/ipsjjip.23.239 (abstract and Section 3, recording Lynch's result).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ZigZagNumberlinkWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NumberlinkWithObstacles

open ZigZagNumberlink (ZigZagNumberlinkInstance rows cols Grid square)

/-!
# NUMBERLINK with obstacles (vertex-disjoint paths in grid graphs) is NP-complete

INSTANCE: an `m × n` board of squares, some of them obstacles (untraversable), and a set of
terminal pairs, each a pair of distinct squares that are not obstacles, with all terminals
distinct. QUESTION: are there pairwise vertex-disjoint paths, one for each terminal pair,
connecting its two terminals, along squares that share a side and avoiding the obstacles?
Squares need not be covered.

This is the Numberlink form without the "cover all vertices" constraint, that is, vertex-disjoint
paths among `k` terminal pairs in a grid graph. Lynch proves it NP-complete; Adcock, Demaine,
Demaine, O'Brien, Reidl, Sánchez Villaamil and Sullivan record the result (abstract: "Lynch's 1975
proof without the 'cover all vertices' constraint"; Section 3: "vertex-disjoint paths among `k`
terminal pairs in grid graphs", whose reduction "allows obstacles (untraversable squares)" and
"does not require every traversable square to be covered by some path"). Membership in NP: the
paths are a certificate.

The board, its squares, adjacency and terminals are those of `ZigZagNumberlinkWanted`, reused
unchanged: the board row by row, a square holding `0` or the pair `c ≥ 1` of its terminal
(`ZigZagNumberlink.square`), the grid graph `pathGraph m □ pathGraph n`
(`ZigZagNumberlink.Grid`), and `ZigZagNumberlink.WellFormed` (a nonempty rectangular board on
which every occurring pair label is on exactly two squares). The obstacles are a list of squares
`(row, column)`. A solution assigns each square the pair whose path uses it, or `0` (`owner`);
for each pair `c` with terminals `s ≠ t`, some path from `s` to `t` contains exactly the squares
owned by `c`, so paths of different pairs are vertex-disjoint, and obstacles are owned by no
pair.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the board (as in `ZigZagNumberlinkWanted`) and the obstacle squares
`(row, column)`. -/
abbrev NumberlinkWithObstaclesInstance := ZigZagNumberlinkInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed ZIG-ZAG NUMBERLINK board, and distinct
obstacles that are squares of the board without a terminal. -/
def WellFormed (i : NumberlinkWithObstaclesInstance) : Prop :=
  ZigZagNumberlink.WellFormed i.1 ∧ i.2.Nodup ∧
    ∀ o ∈ i.2, ∃ x : Fin (rows i.1) × Fin (cols i.1),
      ((x.1 : ℕ), (x.2 : ℕ)) = o ∧ square i.1 x = 0

/-- One owner function on the squares, with every obstacle owned by no label (`0`), such that
for every two distinct squares `s ≠ t` carrying the same positive label `c` some simple path
from `s` to `t` has support exactly the squares owned by `c`. Paths for different pairs of one
label need not be disjoint; on a well-formed board each label is on exactly two squares, so the
paths connect the terminal pairs, are pairwise vertex-disjoint and avoid the obstacles. -/
def NumberlinkWithObstaclesFeasible (i : NumberlinkWithObstaclesInstance) : Prop :=
  ∃ owner : Fin (rows i.1) × Fin (cols i.1) → ℕ,
    (∀ x, ((x.1 : ℕ), (x.2 : ℕ)) ∈ i.2 → owner x = 0) ∧
    ∀ s t, 0 < square i.1 s → square i.1 t = square i.1 s → s ≠ t →
      ∃ p : (Grid i.1).Walk s t, p.IsPath ∧ ∀ x, x ∈ p.support ↔ owner x = square i.1 s

open Classical in
/-- NUMBERLINK with obstacles as a decision problem over bitstrings. -/
noncomputable def numberlinkWithObstaclesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NumberlinkWithObstaclesInstance) x with
  | some i => decide (WellFormed i ∧ NumberlinkWithObstaclesFeasible i)
  | none => false

/-- **NUMBERLINK with obstacles (vertex-disjoint paths in grid graphs) is NP-complete.** Source:
Lynch (1975); Adcock et al. (2015). -/
public theorem_wanted numberlinkWithObstacles_npComplete :
    numberlinkWithObstaclesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L numberlinkWithObstaclesDec

end MetaMathlibExt.Complexity.NPComplete.NumberlinkWithObstacles
