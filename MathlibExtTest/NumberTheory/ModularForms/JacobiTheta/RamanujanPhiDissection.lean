/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanPhiDissection
import Mathlib.Tactic.Ring

open MetaMathlibExt MetaMathlibExt.QPochhammer

-- At zero the products are all one and the shifted residue classes contribute zero.
example : qPochhammerInfRaw 0 0 ^ 2 / qPochhammerInfRaw (0 ^ 2) (0 ^ 2) = 1 := by
  calc
    _ = _ := ramanujanPhi_neg_dissection 0 (by simp)
    _ = 1 := by simp [qPochhammerInfRaw]

-- Twisting the nome by a cube root of unity only scales the correction term.
example {q ω : ℂ} (hq : ‖q‖ < 1) (hω : ω ^ 3 = 1) :
    let phi (z : ℂ) := qPochhammerInfRaw z z ^ 2 / qPochhammerInfRaw (z ^ 2) (z ^ 2)
    phi (ω * q) - phi (q ^ 9) = ω * (phi q - phi (q ^ 9)) := by
  have hnorm : ‖ω‖ = 1 := by
    have h := congrArg norm hω
    rw [norm_pow, norm_one] at h
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : 3 ≠ 0)).mp (by simpa using h)
  have hmul : ‖ω * q‖ < 1 := by simpa [norm_mul, hnorm] using hq
  have hpow (k : ℕ) : (ω * q) ^ (3 * k) = q ^ (3 * k) := by simp [pow_mul, mul_pow, hω]
  dsimp only
  rw [ramanujanPhi_neg_dissection (ω * q) hmul, ramanujanPhi_neg_dissection q hq,
    hpow 3, hpow 6, hpow 1, hpow 2, ← pow_mul]
  ring

#print axioms MetaMathlibExt.ramanujanPhi_neg_dissection
