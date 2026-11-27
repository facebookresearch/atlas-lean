/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.JacobiTheta.PhiSqMulPhiSqTenEisenstein

open MetaMathlibExt

/-- `f_k = (x;x)_∞` at `x = q^k`. -/
local notation "𝔣" x:max => QPochhammer.qPochhammerInfRaw x x
/-- Ramanujan's `φ(x) = f(x,x) = ∑_{n ∈ ℤ} x^{n²}`. -/
local notation "φ" x:max => ramanujanThetaRaw x x
/-- The weight-two Eisenstein series `P(x) = 1 - 24 ∑_{m ≥ 1} m x^m / (1 - x^m)`. -/
local notation "𝐏" x:max =>
  (1 - 24 * tsum fun m : ℕ => ((m + 1 : ℕ) : ℂ) * x ^ (m + 1) / (1 - x ^ (m + 1)))

example (q : ℂ) (hq : ‖q‖ < 1) :
    (φ q) ^ 2 * (φ (q ^ 10)) ^ 2 =
      -(1 / 36) * (𝐏 q - 𝐏 (q ^ 2) + 2 * 𝐏 (q ^ 4) + 5 * 𝐏 (q ^ 5) - 8 * 𝐏 (q ^ 8)
          - 5 * 𝐏 (q ^ 10) + 10 * 𝐏 (q ^ 20) - 40 * 𝐏 (q ^ 40))
        + 10 / 3 * q * (𝔣 (q ^ 2)) ^ 2 * (𝔣 (q ^ 10)) ^ 2
        + 8 / 3 * q ^ 2 * (𝔣 (q ^ 4)) ^ 2 * (𝔣 (q ^ 20)) ^ 2
        + 4 * q ^ 3 * ((𝔣 (q ^ 4)) ^ 5 * 𝔣 (q ^ 10) * (𝔣 (q ^ 40)) ^ 2
          / (𝔣 (q ^ 2) * (𝔣 (q ^ 8)) ^ 2 * 𝔣 (q ^ 20))) :=
  phi_sq_mul_phi_sq_ten_eisenstein (q := q) (hq := hq)

example : ramanujanThetaRaw 0 0 ^ 2 * ramanujanThetaRaw 0 0 ^ 2 = 1 := by
  have h := phi_sq_mul_phi_sq_ten_eisenstein 0 (by simp)
  norm_num [zero_pow (Nat.succ_ne_zero _)] at h
  exact h
