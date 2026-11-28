/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR k-MEANS: definitions

Source:
M. Mahajan, P. Nimbhorkar and K. Varadarajan, "The planar k-means problem is NP-hard",
Theoretical Computer Science 442 (2012), 13-21, doi:10.1016/j.tcs.2010.05.034, Theorem 1
(reduction from planar 3-SAT).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarKMeans

/-- A rational number: the positive and negative parts of its numerator, and its denominator. -/
abbrev RatCode := (ℕ × ℕ) × ℕ

/-- The value of a rational code. -/
def RatCode.val (q : RatCode) : ℚ := ((q.1.1 : ℤ) - q.1.2 : ℤ) / (q.2 : ℚ)

/-- An instance: the points (pairs of rational coordinates), `k`, and the bound `R`. -/
abbrev PlanarKMeansInstance := List (RatCode × RatCode) × ℕ × RatCode

/-- A point of the instance as an element of the Euclidean plane. -/
noncomputable def point (p : RatCode × RatCode) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(p.1.val : ℝ), (p.2.val : ℝ)]

/-- Well-formedness of an instance: all denominators are positive and `k ≥ 1`. -/
def WellFormed (i : PlanarKMeansInstance) : Prop :=
  (∀ p ∈ i.1, 0 < p.1.2 ∧ 0 < p.2.2) ∧ 1 ≤ i.2.1 ∧ 0 < i.2.2.2

/-- Some `k` centers in the plane give every point its squared distance to the nearest center,
with total at most `R`. -/
def PlanarKMeansFeasible (i : PlanarKMeansInstance) : Prop :=
  ∃ c : Fin i.2.1 → EuclideanSpace ℝ (Fin 2),
    (i.1.map fun p => ⨅ j, dist (point p) (c j) ^ 2).sum ≤ (i.2.2.val : ℝ)

open Classical in
/-- PLANAR k-MEANS as a decision problem over bitstrings. -/
noncomputable def planarKMeansDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PlanarKMeansInstance) x with
  | some i => decide (WellFormed i ∧ PlanarKMeansFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PlanarKMeans
