/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.EdmondsGiles
import Mathlib.Tactic.Linarith

/-!
# Tests of the Edmonds-Giles theorem

Upper-bound systems give examples with unbounded feasible region. A rational inequality
with a fractional endpoint illustrates the obstruction to total dual integrality.
-/

open MathlibExt.Analysis.Convex.EdmondsGilesWanted
open MathlibExt.Analysis.Convex.TotalDualIntegrality Matrix

-- Integral upper bounds can be negative.
example {n : ℕ} (b : Fin n → ℤ) (x : Fin n → ℝ)
    (hx : x ∈ Set.extremePoints ℝ {w : Fin n → ℝ | ∀ i, w i ≤ (b i : ℝ)}) :
    ∀ j, ∃ z : ℤ, x j = z := by
  apply extremePoints_integral_of_isTDI (1 : Matrix (Fin n) (Fin n) ℝ) (fun i ↦ (b i : ℝ))
    _ _ (isTDI_upperBound _) x
  · simpa only [one_mulVec, Pi.le_def] using hx
  · intro i j
    refine ⟨if i = j then 1 else 0, ?_⟩
    rw [Matrix.one_apply]
    split <;> norm_num
  · exact fun i ↦ ⟨b i, rfl⟩

-- The endpoint 2/3 of (3/2)x ≤ 1 would have to be integral if this system were TDI.
example : ¬ IsTDI (fun _ _ : Fin 1 ↦ (3 / 2 : ℝ)) (fun _ ↦ 1) := by
  let A : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ 3 / 2
  let x : Fin 1 → ℝ := fun _ ↦ 2 / 3
  have hfeas (w : Fin 1 → ℝ) : A *ᵥ w ≤ (fun _ ↦ 1) ↔ w 0 ≤ 2 / 3 := by
    simp [A, Pi.le_def, mulVec, dotProduct]
    constructor <;> intro h <;> linarith
  have hx : x ∈ Set.extremePoints ℝ {w | A *ᵥ w ≤ (fun _ ↦ 1)} := by
    refine ⟨(hfeas x).mpr le_rfl, ?_⟩
    rintro w hw v hv ⟨s, t, hs, ht, hst, heq⟩
    ext i
    rw [Subsingleton.elim i 0]
    have havg := congrFun heq 0
    change s * w 0 + t * v 0 = 2 / 3 at havg
    apply le_antisymm ((hfeas w).mp hw)
    by_contra! h
    change w 0 < 2 / 3 at h
    linarith [mul_lt_mul_of_pos_left h hs, mul_le_mul_of_nonneg_left ((hfeas v).mp hv) ht.le]
  intro hTDI
  obtain ⟨z, hz⟩ := extremePoints_integral_of_isTDI A (fun _ ↦ 1)
    (fun _ _ ↦ ⟨3 / 2, by norm_num [A]⟩) (fun _ ↦ ⟨1, by simp⟩) hTDI x hx 0
  change (2 / 3 : ℝ) = z at hz
  have hpos : (0 : ℝ) < z := by linarith
  have hlt : (z : ℝ) < 1 := by linarith
  exact (Int.add_one_le_of_lt (by exact_mod_cast hpos)).not_gt (by exact_mod_cast hlt)
