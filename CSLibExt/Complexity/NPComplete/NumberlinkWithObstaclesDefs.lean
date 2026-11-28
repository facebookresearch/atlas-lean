/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NUMBERLINK with obstacles (vertex-disjoint paths in grid graphs): definitions

Source:
J. F. Lynch, "The equivalence of theorem proving and the interconnection problem", ACM SIGDA
Newsletter 5(3) (1975), 31-36, doi:10.1145/1061425.1061430;
A. Adcock, E. D. Demaine, M. L. Demaine, M. P. O'Brien, F. Reidl, F. Sánchez Villaamil, and
B. D. Sullivan, "Zig-zag Numberlink is NP-complete", Journal of Information Processing 23(3)
(2015), 239-245, doi:10.2197/ipsjjip.23.239 (abstract and Section 3, recording Lynch's result).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ZigZagNumberlinkDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NumberlinkWithObstacles

open ZigZagNumberlink (ZigZagNumberlinkInstance rows cols Grid square)

/-- An instance: the board (as in `ZigZagNumberlinkWanted`) and the obstacle squares
`(row, column)`. -/
abbrev NumberlinkWithObstaclesInstance := ZigZagNumberlinkInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed ZIG-ZAG NUMBERLINK board, and distinct
obstacles that are squares of the board without a terminal. -/
def WellFormed (i : NumberlinkWithObstaclesInstance) : Prop :=
  ZigZagNumberlink.WellFormed i.1 ∧ i.2.Nodup ∧
    ∀ o ∈ i.2, ∃ x : Fin (rows i.1) × Fin (cols i.1),
      ((x.1 : ℕ), (x.2 : ℕ)) = o ∧ square i.1 x = 0

/-- Vertex-disjoint paths connect every terminal pair and avoid the obstacles: every obstacle is
owned by no pair (`0`), and for each pair `c` with terminals `s ≠ t` some path from `s` to `t`
passes exactly through the squares owned by `c`. -/
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

end MetaMathlibExt.Complexity.NPComplete.NumberlinkWithObstacles
