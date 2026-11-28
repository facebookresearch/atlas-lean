/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC TRAVELING SALESMAN: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND23] GEOMETRIC TRAVELING SALESMAN;
C. H. Papadimitriou, "The Euclidean travelling salesman problem is NP-complete", Theoretical
Computer Science 4 (1977), 237-244, doi:10.1016/0304-3975(77)90012-3;
M. R. Garey, R. L. Graham and D. S. Johnson, "Some NP-complete geometric problems", Proc.
8th Annual ACM Symposium on Theory of Computing (1976), 10-22, doi:10.1145/800113.803626.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeometricTravelingSalesman

/-- An instance: the points, each a pair of integer coordinates in positive/negative-part
form, and the bound `B`. -/
abbrev GeometricTravelingSalesmanInstance := List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ

/-- The integer `p - q` encoded by the pair `(p, q)`. -/
def toInt (z : ℕ × ℕ) : ℤ := (z.1 : ℤ) - z.2

/-- The point of `Z × Z` encoded by a pair of encoded integers. -/
def point (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ × ℤ := (toInt q.1, toInt q.2)

/-- The discretized Euclidean distance `⌈((x₁ - x₂)² + (y₁ - y₂)²)^(1/2)⌉`. -/
noncomputable def discreteDist (p q : ℤ × ℤ) : ℕ :=
  ⌈Real.sqrt (((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 : ℤ) : ℝ)⌉₊

/-- The length of a tour, given as a list of point positions: the sum of the distances between
consecutive points, including the return to the first. -/
noncomputable def tourLength (P : List (ℤ × ℤ)) (tour : List ℕ) : ℕ :=
  ((List.range tour.length).map fun j =>
    discreteDist (P.getD (tour.getD j 0) (0, 0)) (P.getD (tour.getD ((j + 1) % tour.length) 0) (0, 0))).sum

/-- Well-formedness of an instance: `P` is a nonempty set of distinct points, and `B` is
positive. -/
def WellFormed (i : GeometricTravelingSalesmanInstance) : Prop :=
  0 < i.1.length ∧ (i.1.map point).Nodup ∧ 0 < i.2

/-- Some tour of the points has length at most `B`. -/
def GeometricTravelingSalesmanFeasible (i : GeometricTravelingSalesmanInstance) : Prop :=
  ∃ tour : List ℕ, tour.Perm (List.range i.1.length) ∧ tourLength (i.1.map point) tour ≤ i.2

open Classical in
/-- GEOMETRIC TRAVELING SALESMAN as a decision problem over bitstrings. -/
noncomputable def geometricTravelingSalesmanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeometricTravelingSalesmanInstance) x with
  | some i => decide (WellFormed i ∧ GeometricTravelingSalesmanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeometricTravelingSalesman
