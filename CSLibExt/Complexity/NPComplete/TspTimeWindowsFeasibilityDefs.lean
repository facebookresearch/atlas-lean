/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRAVELING SALESMAN WITH TIME WINDOWS: FEASIBILITY: definitions

Source:
M. W. P. Savelsbergh, "Local search in routing problems with time windows", Annals of
Operations Research 4 (1985), 285-305, doi:10.1007/BF02022044;
M. W. P. Savelsbergh, *Computer Aided Routing*, CWI Tract 75, Centrum voor Wiskunde en
Informatica, Amsterdam (1992), Section 4.1, pp. 19-20 (the statement and proof: "The problem
of determining whether there exists a feasible tour for the TSPTW is NP-complete in the strong
sense").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TspTimeWindowsFeasibility

/-- An instance: the travel times as `n + 2` rows of `n + 2` entries (`t_ij` is entry `j` of
row `i`), and one time window `(e_i, l_i)` per vertex `i = 0, …, n + 1`. -/
abbrev TspTimeWindowsFeasibilityInstance := List (List ℕ) × List (ℕ × ℕ)

/-- The number of vertices, `n + 2`: one per listed time window. -/
def numVertices (i : TspTimeWindowsFeasibilityInstance) : ℕ := i.2.length

/-- The travel time `t_ab`: entry `b` of row `a` (`0` outside the matrix). -/
def travelTime (i : TspTimeWindowsFeasibilityInstance) (a b : ℕ) : ℕ :=
  (i.1.getD a []).getD b 0

/-- The earliest service time `e_a` of vertex `a`. -/
def earliest (i : TspTimeWindowsFeasibilityInstance) (a : ℕ) : ℕ :=
  (i.2.getD a (0, 0)).1

/-- The latest service time `l_a` of vertex `a`. -/
def latest (i : TspTimeWindowsFeasibilityInstance) (a : ℕ) : ℕ :=
  (i.2.getD a (0, 0)).2

/-- Well-formedness of an instance: there are at least two vertices (the origin `0` and the
destination `n + 1`), the travel-time matrix has one row per vertex and one entry per vertex
in each row, and it is symmetric, `t_ab = t_ba`, and satisfies the triangle inequality,
`t_ac ≤ t_ab + t_bc`. -/
def WellFormed (i : TspTimeWindowsFeasibilityInstance) : Prop :=
  2 ≤ numVertices i ∧ i.1.length = numVertices i ∧
    (∀ row ∈ i.1, row.length = numVertices i) ∧
    (∀ a < numVertices i, ∀ b < numVertices i, travelTime i a b = travelTime i b a) ∧
    ∀ a < numVertices i, ∀ b < numVertices i, ∀ c < numVertices i,
      travelTime i a c ≤ travelTime i a b + travelTime i b c

/-- A feasible tour exists: a path listing every vertex exactly once, from the origin `0` to
the destination `n + 1`, and service times `D` within every vertex's window with
`D_a + t_ab ≤ D_b` for each pair `a, b` of consecutive vertices on the path. -/
def TspTimeWindowsFeasible (i : TspTimeWindowsFeasibilityInstance) : Prop :=
  ∃ path : List ℕ, path.Perm (List.range (numVertices i)) ∧ path.head? = some 0 ∧
    path.getLast? = some (numVertices i - 1) ∧
    ∃ D : ℕ → ℕ, (∀ a < numVertices i, earliest i a ≤ D a ∧ D a ≤ latest i a) ∧
      ∀ p ∈ path.zip path.tail, D p.1 + travelTime i p.1 p.2 ≤ D p.2

open Classical in
/-- TRAVELING SALESMAN WITH TIME WINDOWS: FEASIBILITY as a decision problem over bitstrings. -/
noncomputable def tspTimeWindowsFeasibilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TspTimeWindowsFeasibilityInstance) x with
  | some i => decide (WellFormed i ∧ TspTimeWindowsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TspTimeWindowsFeasibility
