/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# s-CLUB: definitions

Source:
B. Balasundaram, S. Butenko and S. Trukhanov, "Novel approaches for analyzing biological
networks", Journal of Combinatorial Optimization 10(1) (2005), 23-39,
doi:10.1007/s10878-005-1857-x;
S. Hartung, C. Komusiewicz and A. Nichterlein, "On structural parameterizations for the 2-club
problem", SOFSEM 2013, Lecture Notes in Computer Science 7741 (2013), 233-243,
doi:10.1007/978-3-642-35843-2_21 (Section 1: the problem statement, and "For all `s ≥ 1`,
s-Club is NP-complete on graphs of diameter `s+1`", citing Balasundaram, Butenko and
Trukhanov).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SClub

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, and the size bound `K`. -/
abbrev SClubInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : SClubInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate edges in
either orientation, no self-loops, endpoints in range), and `K` is positive. -/
def WellFormed (i : SClubInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    1 ≤ i.2.2

/-- There is a set `S` of at least `K` vertices whose induced subgraph has diameter at most
`s`. -/
def SClubFeasible (s : ℕ) (i : SClubInstance) : Prop :=
  ∃ S : Finset (Fin i.1), i.2.2 ≤ S.card ∧
    ((Graph i).induce (S : Set (Fin i.1))).ediam ≤ (s : ℕ∞)

open Classical in
/-- s-CLUB, for the fixed diameter bound `s`, as a decision problem over bitstrings. -/
noncomputable def sClubDec (s : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SClubInstance) x with
  | some i => decide (WellFormed i ∧ SClubFeasible s i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SClub
