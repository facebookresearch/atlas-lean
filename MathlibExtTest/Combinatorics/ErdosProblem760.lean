/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ErdosProblem760
import Mathlib.Tactic.Positivity

/-! # Boundary cases and complete graphs for the cochromatic subgraph bounds -/

open SimpleGraph MathlibExt.Combinatorics.ErdosProblem760Wanted

-- The linear bound gives a single constant for all complete graphs.
example : ∃ c > (0 : ℝ), ∀ m : ℕ, 2 ≤ m →
    ∃ H : (⊤ : SimpleGraph (Fin m)).Subgraph, ∃ k : ℕ,
      (k : ℕ∞) ≤ H.coe.cochromaticNumber ∧ c * m ≤ k * Real.log m := by
  obtain ⟨c, hc, h⟩ := conjecture_holds.{0, 0}.1
  refine ⟨c, hc, fun m hm => ?_⟩
  obtain ⟨H, k, hk, hb⟩ := h (Fin m) ⊤ m (by simp)
  have hm' : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  exact ⟨H, k, hk, (div_le_iff₀ (Real.log_pos hm')).mp hb⟩

-- At chromatic numbers zero and one, the empty subgraph witnesses both bounds.
example {V : Type*} (G : SimpleGraph V) {m : ℕ} (hm : m ≤ 1) (c : ℝ) :
    ∃ H : G.Subgraph, (0 : ℕ∞) ≤ H.coe.cochromaticNumber ∧
      c * m / Real.log m ≤ 0 ∧ c * Real.sqrt (m / Real.log m) ≤ 0 := by
  refine ⟨⊥, by simp, ?_⟩
  have h : m = 0 ∨ m = 1 := by omega
  rcases h with rfl | rfl <;> simp

-- From two vertices onwards the square-root bound forces a strictly positive witness.
example (m : ℕ) (hm : 2 ≤ m) :
    ∃ H : (⊤ : SimpleGraph (Fin m)).Subgraph, 0 < H.coe.cochromaticNumber := by
  obtain ⟨c, hc, h⟩ := conjecture_holds.{0, 0}.2
  obtain ⟨H, k, hk, hb⟩ := h (Fin m) ⊤ m (by simp)
  have hm' : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hpos := Real.log_pos hm'
  have hbound : 0 < c * Real.sqrt (m / Real.log m) :=
    mul_pos hc (Real.sqrt_pos_of_pos (div_pos (zero_lt_one.trans hm') hpos))
  have hk' : 0 < k := by exact_mod_cast hbound.trans_le hb
  exact ⟨H, (show 0 < (k : ℕ∞) by exact_mod_cast hk').trans_le hk⟩
