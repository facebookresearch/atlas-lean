/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.ControlTheory.StateSpace.Coefficients

/-!
# Discrete-time state-space trajectories

For `ControlTheory.StateSpaceCoeffs` and an input sequence `u : ℕ → U`,
`StateSpaceCoeffs.dtTraj` is the trajectory `x 0 = x0`,
`x (k + 1) = A (x k) + B (u k)`. It is the unique such sequence, and it
has the closed form
`x k = A^k x0 + ∑ j < k, A^(k - 1 - j) (B (u j))`.
`StateSpaceCoeffs.dtOutput` is the output `y k = C (x k) + D (u k)`.
-/

@[expose] public section

namespace ControlTheory

namespace StateSpaceCoeffs

/-- The discrete-time trajectory of the coefficients `S` with input
sequence `u` and initial state `x0`: `x 0 = x0` and
`x (k + 1) = A (x k) + B (u k)`. -/
def dtTraj {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) (u : ℕ → U) (x0 : X) : ℕ → X
  | 0 => x0
  | k + 1 => S.A (dtTraj S u x0 k) + S.B (u k)

/-- The discrete-time output of the coefficients `S` along the
trajectory with input `u` and initial state `x0`:
`y k = C (x k) + D (u k)`. -/
def dtOutput {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) (u : ℕ → U) (x0 : X) (k : ℕ) : Y :=
  S.C (dtTraj S u x0 k) + S.D (u k)

theorem dtTraj_zero {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) (u : ℕ → U) (x0 : X) :
    dtTraj S u x0 0 = x0 := by
  rfl

theorem dtTraj_succ {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) (u : ℕ → U) (x0 : X) (k : ℕ) :
    dtTraj S u x0 (k + 1) = S.A (dtTraj S u x0 k) + S.B (u k) := by
  rfl

/-- Closed form of the discrete-time trajectory:
`x k = A^k x0 + ∑ j < k, A^(k - 1 - j) (B (u j))`, where `A^k` is the
`k`-fold composite of the continuous linear map `A`. -/
theorem dtTraj_closedForm {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) (u : ℕ → U) (x0 : X) (k : ℕ) :
    dtTraj S u x0 k
      = (S.A ^ k) x0 + ∑ j ∈ Finset.range k, (S.A ^ (k - 1 - j)) (S.B (u j)) := by
  induction k with
  | zero =>
      rw [dtTraj_zero, pow_zero, one_apply_eq_self, Finset.sum_range_zero, add_zero]
  | succ k ih =>
      rw [dtTraj_succ, ih, Finset.sum_range_succ]
      have hlast : k + 1 - 1 - k = 0 := by omega
      rw [hlast, pow_zero, one_apply_eq_self]
      rw [map_add, map_sum]
      have hPow : S.A ((S.A ^ k) x0) = (S.A ^ (k + 1)) x0 := by
        rw [pow_succ', mul_apply_eq_comp]
      have hSum : (∑ j ∈ Finset.range k, S.A ((S.A ^ (k - 1 - j)) (S.B (u j))))
          = ∑ j ∈ Finset.range k, (S.A ^ (k + 1 - 1 - j)) (S.B (u j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < k := Finset.mem_range.mp hj
        have hexp : k + 1 - 1 - j = (k - 1 - j) + 1 := by omega
        rw [hexp, pow_succ', mul_apply_eq_comp]
      rw [hPow, hSum, add_assoc]

/-- Uniqueness of the discrete-time trajectory: any sequence starting
at `x0` and satisfying the recursion equals `dtTraj S u x0`. -/
theorem dtTraj_unique {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) (u : ℕ → U) (x0 : X) {x : ℕ → X}
    (hx0 : x 0 = x0)
    (hx : ∀ k, x (k + 1) = S.A (x k) + S.B (u k)) :
    x = dtTraj S u x0 := by
  funext k
  induction k with
  | zero => rw [hx0, dtTraj_zero]
  | succ k ih => rw [hx, ih, dtTraj_succ]

theorem dtOutput_apply {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) (u : ℕ → U) (x0 : X) (k : ℕ) :
    dtOutput S u x0 k = S.C (dtTraj S u x0 k) + S.D (u k) := by
  rfl

/-- Closed form of the discrete-time output, from
`dtTraj_closedForm`. -/
theorem dtOutput_closedForm {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) (u : ℕ → U) (x0 : X) (k : ℕ) :
    dtOutput S u x0 k
      = S.C ((S.A ^ k) x0 + ∑ j ∈ Finset.range k, (S.A ^ (k - 1 - j)) (S.B (u j)))
        + S.D (u k) := by
  rw [dtOutput_apply, dtTraj_closedForm]

end StateSpaceCoeffs

end ControlTheory
