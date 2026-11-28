/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HIROIMONO (Goishi Hiroi): definitions

Source:
D. Andersson, "HIROIMONO is NP-complete", BRICS Report Series RS-07-1, University of Aarhus
(2007), doi:10.7146/brics.v14i1.21924, Definition 1 and Theorem 1 (conference version: Fun with
Algorithms (FUN 2007), Lecture Notes in Computer Science 4475 (2007), 30-39,
doi:10.1007/978-3-540-72914-3_5).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Hiroimono

/-- An instance: the list of stones, each a point of `Z²` given by two encoded integers. -/
abbrev HiroimonoInstance := List ((ℕ × ℕ) × (ℕ × ℕ))

/-- The stones as points of `ℤ × ℤ`. -/
def stones (i : HiroimonoInstance) : List (ℤ × ℤ) :=
  i.map GeometricTravelingSalesman.point

/-- Well-formedness of an instance: a nonempty list of distinct points. -/
def WellFormed (i : HiroimonoInstance) : Prop :=
  i ≠ [] ∧ (stones i).Nodup

/-- `c` lies strictly between `a` and `b` on a common vertical or horizontal grid line. -/
def StrictlyBetween (a b c : ℤ × ℤ) : Prop :=
  (a.1 = b.1 ∧ c.1 = a.1 ∧ min a.2 b.2 < c.2 ∧ c.2 < max a.2 b.2) ∨
    (a.2 = b.2 ∧ c.2 = a.2 ∧ min a.1 b.1 < c.1 ∧ c.1 < max a.1 b.1)

/-- The direction of the move from `a` to `b`: the componentwise sign of `b - a` (a unit vector
for a move along a grid line). -/
def direction (a b : ℤ × ℤ) : ℤ × ℤ :=
  ((b.1 - a.1).sign, (b.2 - a.2).sign)

/-- The puzzle is solvable: some order of picking up all the stones moves along grid lines
between consecutive stones, passes only stones already picked up, and makes no 180° turn. -/
def HiroimonoFeasible (i : HiroimonoInstance) : Prop :=
  ∃ order : List (ℤ × ℤ), order.Perm (stones i) ∧
    ∀ k, ∀ hk : k + 1 < order.length,
      (order[k].1 = order[k + 1].1 ∨ order[k].2 = order[k + 1].2) ∧
      (∀ c ∈ stones i, StrictlyBetween order[k] order[k + 1] c → c ∈ order.take k) ∧
      (0 < k → direction order[k - 1] order[k] ≠ -direction order[k] order[k + 1])

open Classical in
/-- HIROIMONO as a decision problem over bitstrings. -/
noncomputable def hiroimonoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HiroimonoInstance) x with
  | some i => decide (WellFormed i ∧ HiroimonoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Hiroimono
