/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Robotics.Hybrid.DwellDivergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

open Robotics.Hybrid

-- Constant unit durations: elapsed time after `n` steps
-- is exactly `n`, and the lower bound is tight.
example (n : ℕ) : dwellElapsed (fun _ => 1) n = n := by
  unfold dwellElapsed
  simp

-- No positive dwell bounds the geometric durations
-- `2 ^ (-k)` from below.
example : ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ, δ ≤ (2 : ℝ) ^ (-(k : ℤ)) := by
  rintro ⟨δ, hδ, hle⟩
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hδ)).exists
  have h2 : (2 : ℝ) ^ (-(n : ℤ)) = (1 / 2) ^ n := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, one_div]
  linarith [hle n]

-- Elapsed time at step `0` is `0`.
example (d : ℕ → ℝ) : dwellElapsed d 0 = 0 := by
  unfold dwellElapsed
  simp

-- Finitely many events: durations `1 + k` are at least `1`,
-- so only finitely many step counts end by `t = 10`.
example : {n : ℕ | dwellElapsed (fun k => 1 + (k : ℝ)) n ≤ 10}.Finite :=
  (events_finite_of_dwell one_pos (fun k => by simp) 10).1

-- Unit durations reach the horizon `3` after exactly `3`
-- steps: the bound `n * δ ≤ H` is attained, and no count
-- above `3` stays within the horizon.
example : dwellElapsed (fun _ => (1 : ℝ)) 3 ≤ 3 ∧
    ∀ n, dwellElapsed (fun _ => (1 : ℝ)) n ≤ 3 → n ≤ 3 := by
  refine ⟨by simp [dwellElapsed], fun n hn => ?_⟩
  have h := (events_finite_of_dwell one_pos (fun _ => le_refl (1 : ℝ)) 3).2 n hn
  exact_mod_cast (by linarith : (n : ℝ) ≤ 3)

-- Boundary horizon `H = 0`: only the zero-step count ends
-- by time `0`.
example : {n : ℕ | dwellElapsed (fun _ => (1 : ℝ)) n ≤ 0} = {0} := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  refine ⟨fun hn => ?_, fun hn => by simp [hn, dwellElapsed]⟩
  have h := (events_finite_of_dwell one_pos (fun _ => le_refl (1 : ℝ)) 0).2 n hn
  exact Nat.eq_zero_of_le_zero (by exact_mod_cast (by linarith : (n : ℝ) ≤ 0))

-- The positive dwell is needed: zero durations satisfy the
-- dwell bound with `δ = 0`, but every step count ends by
-- time `0`.
example : ¬ {n : ℕ | dwellElapsed (fun _ => (0 : ℝ)) n ≤ 0}.Finite := by
  have h : {n : ℕ | dwellElapsed (fun _ => (0 : ℝ)) n ≤ 0} = Set.univ :=
    Set.eq_univ_of_forall fun n => by simp [dwellElapsed]
  rw [h]
  exact Set.infinite_univ

#print axioms dwellElapsed_ge
#print axioms dwellElapsed_tendsto_atTop
#print axioms events_finite_of_dwell
