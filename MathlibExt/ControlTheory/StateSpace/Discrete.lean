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
The Markov parameters `markov 0 = D`, `markov (k+1) = C ∘ A^k ∘ B`
give the zero-state output as their causal convolution with the input,
and the unit-sample response is exactly the Markov sequence.
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

/-- Markov parameters of the coefficients: `markov 0 = D` and
`markov (k+1) = C ∘ A^k ∘ B` as continuous linear maps. -/
def markov {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) : ℕ → (U →L[𝕜] Y)
  | 0 => S.D
  | k + 1 => S.C.comp ((S.A ^ k).comp S.B)

theorem markov_zero {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) : S.markov 0 = S.D := by
  rfl

theorem markov_succ {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) (k : ℕ) :
    S.markov (k + 1) = S.C.comp ((S.A ^ k).comp S.B) := by
  rfl

private theorem markov_succ_apply {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) (k : ℕ) (v : U) :
    S.markov (k + 1) v = S.C ((S.A ^ k) (S.B v)) := by
  rw [markov_succ]
  rfl

/-- Zero-state output is the causal convolution of the input with the
Markov parameters: `y n = ∑ k ≤ n, markov k (u (n-k))`. -/
theorem zeroState_output_eq_sum_markov {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) (u : ℕ → U) (n : ℕ) :
    S.dtOutput u 0 n = ∑ k ∈ Finset.range (n + 1), S.markov k (u (n - k)) := by
  show S.C (dtTraj S u 0 n) + S.D (u n)
    = ∑ k ∈ Finset.range (n + 1), S.markov k (u (n - k))
  rw [dtTraj_closedForm, map_zero, zero_add, map_sum, Finset.sum_range_succ']
  have h0 : n - 0 = n := by omega
  rw [h0, markov_zero]
  congr 1
  have hRefl := Finset.sum_range_reflect
    (fun k => S.C ((S.A ^ k) (S.B (u (n - 1 - k))))) n
  have hRHS : (∑ k ∈ Finset.range n, S.markov (k + 1) (u (n - (k + 1))))
      = ∑ k ∈ Finset.range n, S.C ((S.A ^ k) (S.B (u (n - 1 - k)))) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [markov_succ_apply]
    have hk1 : n - (k + 1) = n - 1 - k := by omega
    rw [hk1]
  rw [hRHS]
  have hLHS : (∑ j ∈ Finset.range n, S.C ((S.A ^ (n - 1 - j)) (S.B (u j))))
      = ∑ j ∈ Finset.range n,
        (fun k => S.C ((S.A ^ k) (S.B (u (n - 1 - k))))) (n - 1 - j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < n := Finset.mem_range.mp hj
    have hjj : n - 1 - (n - 1 - j) = j := by omega
    show S.C ((S.A ^ (n - 1 - j)) (S.B (u j)))
      = S.C ((S.A ^ (n - 1 - j)) (S.B (u (n - 1 - (n - 1 - j)))))
    rw [hjj]
  rw [hLHS]
  exact hRefl

/-- The response to a unit sample input `v` at time `0` (and `0`
afterwards) is exactly the Markov sequence applied to `v`. -/
theorem dtOutput_unitSample {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) (v : U) (n : ℕ) :
    S.dtOutput (fun k => if k = 0 then v else 0) 0 n = S.markov n v := by
  rw [zeroState_output_eq_sum_markov]
  have hfn : S.markov n ((fun k => if k = 0 then v else 0) (n - n)) = S.markov n v := by
    have hnn : n - n = 0 := by omega
    show S.markov n (if n - n = 0 then v else 0) = S.markov n v
    rw [ite_eq_left hnn]
  rw [← hfn]
  refine Finset.sum_eq_single n ?_ ?_
  · intro k hk hkn
    have hklt : k < n + 1 := Finset.mem_range.mp hk
    have hnk : n - k ≠ 0 := by omega
    show S.markov k (if n - k = 0 then v else 0) = 0
    rw [ite_eq_right hnk, map_zero]
  · intro hcon
    have hmem : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_self n)
    exact absurd hmem hcon

end StateSpaceCoeffs

end ControlTheory
