/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EUCLIDEAN p-CENTER: definitions

Source:
N. Megiddo and K. J. Supowit, "On the complexity of some common geometric location
problems", SIAM Journal on Computing 13 (1984), 182-196, doi:10.1137/0213014;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM GEOMETRIC DISK COVER.
-/
module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EuclideanPCenter

open GeometricTravelingSalesman (point)

/-- An instance: the points (pairs of encoded integers), the number `p` of disks, and the
radius `r` as a pair `(num, den)` standing for `num / den`. -/
abbrev EuclideanPCenterInstance := List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ × (ℕ × ℕ)

/-- The radius `r = num / den` of the instance. -/
noncomputable def radius (i : EuclideanPCenterInstance) : ℝ :=
  (i.2.2.1 : ℝ) / i.2.2.2

/-- Well-formedness of an instance: the points are distinct, `p` is positive, and the radius
`num / den` has a positive denominator and is positive. -/
def WellFormed (i : EuclideanPCenterInstance) : Prop :=
  (i.1.map point).Nodup ∧ 0 < i.2.1 ∧ 0 < i.2.2.2 ∧ 0 < i.2.2.1

/-- Some `p` centers in the plane put every point within Euclidean distance `r` of one of
them. -/
def EuclideanPCenterFeasible (i : EuclideanPCenterInstance) : Prop :=
  ∃ c : Fin i.2.1 → ℝ × ℝ, ∀ q ∈ i.1, ∃ j,
    ((point q).1 - (c j).1) ^ 2 + ((point q).2 - (c j).2) ^ 2 ≤ radius i ^ 2

open Classical in
/-- EUCLIDEAN p-CENTER as a decision problem over bitstrings. -/
noncomputable def euclideanPCenterDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EuclideanPCenterInstance) x with
  | some i => decide (WellFormed i ∧ EuclideanPCenterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EuclideanPCenter
