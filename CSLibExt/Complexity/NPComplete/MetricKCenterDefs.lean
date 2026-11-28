/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC K-CENTER: definitions

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MINIMUM K-CENTER;
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. I: The
p-centers", SIAM Journal on Applied Mathematics 37 (1979), 513-538, doi:10.1137/0137040.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.KCenterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricKCenter

open KCenter (KCenterInstance KCenterFeasible)

/-- The distance `d(u, v)`: entry `v` of row `u` of the matrix. -/
def distance (i : KCenterInstance) (u v : ℕ) : ℕ := (i.1.getD u []).getD v 0

/-- Well-formedness of an instance: the parent's condition, a square matrix that is a metric
(zero exactly on the diagonal, symmetric, triangle inequality), `0 < k ≤ |V|`, and `0 < B`. -/
def WellFormed (i : KCenterInstance) : Prop :=
  KCenter.WellFormed i ∧ (∀ row ∈ i.1, row.length = i.1.length) ∧
    (∀ u < i.1.length, ∀ v < i.1.length, distance i u v = 0 ↔ u = v) ∧
    (∀ u < i.1.length, ∀ v < i.1.length, distance i u v = distance i v u) ∧
    (∀ u < i.1.length, ∀ v < i.1.length, ∀ w < i.1.length,
      distance i u w ≤ distance i u v + distance i v w) ∧
    0 < i.2.1 ∧ i.2.1 ≤ i.1.length ∧ 0 < i.2.2

open Classical in
/-- METRIC K-CENTER as a decision problem over bitstrings. -/
noncomputable def metricKCenterDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KCenterInstance) x with
  | some i => decide (WellFormed i ∧ KCenterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MetricKCenter
