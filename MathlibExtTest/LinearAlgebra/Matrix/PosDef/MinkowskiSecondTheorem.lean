/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.PosDef.MinkowskiSecondTheorem
import Mathlib.Algebra.Order.Star.Real

open Matrix

variable {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ}

-- The weak form of Minkowski's second theorem, for any greedy minima and for the chosen ones.
example (hY : Y.PosDef) {v : Fin g → Fin g → ℤ} (hv : IsGreedyMinima Y v) :
    ∏ k, (Int.cast ∘ v k : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ v k) ≤ (g : ℝ) ^ g * Y.det :=
  hv.prod_le_pow_mul_det hY

example (hY : Y.PosDef) : ∏ k, hY.succMin k ≤ (g : ℝ) ^ g * Y.det :=
  hY.prod_succMin_le_pow_mul_det

-- For the identity matrix, the bound reads `∏ λ_k ≤ g ^ g`.
example : ∏ k, (PosDef.one : (1 : Matrix (Fin g) (Fin g) ℝ).PosDef).succMin k ≤ (g : ℝ) ^ g := by
  simpa using (PosDef.one : (1 : Matrix (Fin g) (Fin g) ℝ).PosDef).prod_succMin_le_pow_mul_det

-- With `λ_k ≥ λ₁`, it gives Minkowski's first theorem in the form `λ₁ ^ g ≤ g ^ g det Y`.
example (hY : Y.PosDef) (hg : 0 < g) : hY.succMin ⟨0, hg⟩ ^ g ≤ (g : ℝ) ^ g * Y.det := by
  refine le_trans ?_ hY.prod_succMin_le_pow_mul_det
  calc hY.succMin ⟨0, hg⟩ ^ g = ∏ _k : Fin g, hY.succMin ⟨0, hg⟩ := by simp
    _ ≤ ∏ k, hY.succMin k := by
        gcongr with k
        · exact fun _ _ ↦ (hY.succMin_pos _).le
        · exact hY.monotone_succMin (Fin.le_def.mpr (Nat.zero_le _))
