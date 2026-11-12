/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib

namespace StatMech

namespace RSW

namespace Push












theorem rpu_push_lower (g : ℕ → ℝ) {β : ℝ} (hβ : 0 < β) (hbase : β ≤ g 0)
    (hstep : ∀ j, g j * β ≤ g (j + 1)) :
    ∀ j, β ^ (j + 1) ≤ g j := by
  intro j
  induction j with
  | zero => simpa using hbase
  | succ j ih =>
    calc β ^ (j + 1 + 1) = β ^ (j + 1) * β := by ring
      _ ≤ g j * β := by
        apply mul_le_mul_of_nonneg_right ih hβ.le
      _ ≤ g (j + 1) := hstep j





theorem rpu_push_constant_pos (g : ℕ → ℝ) {β : ℝ} (hβ : 0 < β) (hbase : β ≤ g 0)
    (hstep : ∀ j, g j * β ≤ g (j + 1)) :
    ∀ j, 0 < g j := by
  intro j
  exact lt_of_lt_of_le (by positivity) (rpu_push_lower g hβ hbase hstep j)




theorem rpu_push_constant_eq {β : ℝ} (j : ℕ) :
    (fun i => β ^ (i + 1)) (j + 1) = (fun i => β ^ (i + 1)) j * β := by
  simp only
  ring



















theorem rpu_push (g : ℕ → ℕ → ℝ) {β : ℝ} (hβ : 0 < β)
    (hbase : ∀ n, β ≤ g 0 n) (hstep : ∀ j n, g j n * β ≤ g (j + 1) n) :
    ∀ j, ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ g j n := by
  intro j
  refine ⟨β ^ (j + 1), by positivity, fun n => ?_⟩
  exact rpu_push_lower (fun i => g i n) hβ (hbase n) (fun i => hstep i n) j

end Push

end RSW

end StatMech
