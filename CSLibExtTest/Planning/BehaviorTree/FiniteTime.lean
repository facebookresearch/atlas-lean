/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Planning.BehaviorTree.FiniteTime

/-! # Bounded versus pointwise success of a countdown -/

open Cslib.Planning.BehaviorTree

namespace CSLibExtTest.BehaviorTree

variable (δ : TimeStep)

private def countdown : Tree ℕ δ where
  next n := n - 1
  status n := if n = 0 then .success else .running

private theorem countdown_stateAt (x k : ℕ) : (countdown δ).stateAt x k = x - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Tree.stateAt_succ, ih]
    change x - k - 1 = x - (k + 1)
    omega

-- On 0 < x ≤ N, a single physical-time bound N * δ works. The hit is at tick x,
-- and the earlier samples are positive and still at most N.
example (N : ℕ) : (countdown δ).FiniteTimeSuccessful {x | 0 < x ∧ x ≤ N} := by
  refine ⟨fun x hx => ?_, N * δ.val, fun x hx => ?_⟩
  · simp [countdown, Nat.ne_of_gt hx.1]
  · refine ⟨x, ?_, ?_, ?_⟩
    · simpa [sampleTime] using
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hx.2 : (x : ℝ) ≤ N) δ.property.le
    · rw [countdown_stateAt]
      simp [countdown]
    · intro j hj
      change 0 < (countdown δ).stateAt x j ∧ (countdown δ).stateAt x j ≤ N
      rw [countdown_stateAt]
      exact ⟨by omega, (Nat.sub_le ..).trans hx.2⟩

-- Every positive start succeeds and stays positive before its hit ...
example (x : ℕ) (hx : 0 < x) : ∃ k > 0, (countdown δ).stateAt x k ∈ (countdown δ).region .success ∧
    ∀ j < k, 0 < (countdown δ).stateAt x j := by
  refine ⟨x, hx, by rw [countdown_stateAt]; simp [countdown], ?_⟩
  intro j hj
  rw [countdown_stateAt]
  omega

-- ... but no single physical-time bound serves *all* positive starts.
example : ¬ (countdown δ).FiniteTimeSuccessful {x | 0 < x} := by
  intro h
  obtain ⟨_, N, hN⟩ := (Tree.finiteTimeSuccessful_iff_tickBound ..).mp h
  obtain ⟨k, hk, hs, _⟩ := hN (N + 1) (Nat.succ_pos N)
  have hp : N + 1 - k ≠ 0 := by omega
  rw [countdown_stateAt] at hs
  simp [countdown, hp] at hs

-- The countdown from 2 reaches success, but it leaves the proposed region {2} first.
example : ¬ (countdown δ).FiniteTimeSuccessful {2} := by
  rintro ⟨_, _, h⟩
  obtain ⟨k, _, hs, hpre⟩ := h 2 rfl
  rw [countdown_stateAt] at hs
  have hk : 2 - k = 0 := by simpa [countdown] using hs
  have hbad : (1 : ℕ) = 2 := hpre 1 (by omega)
  contradiction

-- A return to running after success does not invalidate a first hit.
example : let T : Tree Bool δ := ⟨not, fun b => if b then .running else .success⟩
    T.FiniteTimeSuccessful {true} ∧ T.status (T.stateAt true 2) = .running := by
  dsimp only
  refine ⟨⟨?_, sampleTime δ 0 1, ?_⟩, rfl⟩
  · rintro b (rfl : b = true)
    rfl
  · rintro b (rfl : b = true)
    refine ⟨1, le_rfl, rfl, fun j hj => ?_⟩
    have : j = 0 := by omega
    subst j
    rfl

end CSLibExtTest.BehaviorTree
