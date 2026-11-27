/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SomosLikeRoots
import Mathlib.Tactic.NormNum

open Filter Topology MetaMathlibExt

-- For k = 2 and a starting value above the Somos constant, the first two roots coincide.
example :
    let σ := Real.exp (∑' m : ℕ, Real.log m / (2 : ℝ) ^ m)
    let t : ℕ → ℝ := Nat.rec (σ + 1) (fun n x => x ^ 2 / (n + 1))
    t 1 ^ (1 / 2 : ℝ) = t 0 ∧
      ∃ c : ℝ, 1 < c ∧ Antitone (fun n : ℕ => t n ^ ((1 : ℝ) / (2 : ℝ) ^ n)) ∧
        Tendsto (fun n : ℕ => t n ^ ((1 : ℝ) / (2 : ℝ) ^ n)) atTop (𝓝 c) := by
  intro σ t
  have ht (n : ℕ) : t (n + 1) = t n ^ 2 / (n + 1) := rfl
  have h0 : σ < t 0 := lt_add_of_pos_right σ zero_lt_one
  refine ⟨?_, somosLike_root_antitone_tendsto 2 le_rfl t (ht := ht) (h0 := h0)⟩
  have ht₀ : 0 ≤ t 0 := (show 0 < σ from Real.exp_pos _).le.trans h0.le
  have hfirst : t 1 = t 0 ^ 2 := by simpa using ht 0
  rw [hfirst, ← Real.rpow_natCast_mul ht₀]
  norm_num
