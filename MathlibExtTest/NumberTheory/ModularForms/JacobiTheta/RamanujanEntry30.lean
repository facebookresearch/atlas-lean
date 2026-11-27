/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanEntry30
import Mathlib.Tactic.Ring

open MetaMathlibExt

-- With `a = b = q`, the product identity (i) is the classical `ψ(q)² = φ(q) ψ(q²)`.
example {q : ℂ} (h : ‖q * q‖ < 1) :
    ramanujanThetaRaw q (q ^ 3) ^ 2 =
      ramanujanThetaRaw q q * ramanujanThetaRaw (q ^ 2) (q ^ 6) := by
  have h₁ := (ramanujanTheta_entry30 q q h).1
  rw [show q * q ^ 2 = q ^ 3 by ring, show q ^ 2 * q = q ^ 3 by ring,
    show (q * q) ^ 3 = q ^ 6 by ring, show q * q = q ^ 2 by ring] at h₁
  rw [sq, h₁]

-- With `a = b = q`, the even part (ii) is the classical `φ(q) + φ(-q) = 2 φ(q⁴)`.
example {q : ℂ} (h : ‖q * q‖ < 1) :
    ramanujanThetaRaw q q + ramanujanThetaRaw (-q) (-q) =
      2 * ramanujanThetaRaw (q ^ 4) (q ^ 4) := by
  have h₂ := (ramanujanTheta_entry30 q q h).2.1
  rwa [show q ^ 3 * q = q ^ 4 by ring, show q * q ^ 3 = q ^ 4 by ring] at h₂

-- With `a = b = q ≠ 0`, the odd part (iii) has the unit first parameter `b / a = 1`.
example {q : ℂ} (hq : q ≠ 0) (h : ‖q * q‖ < 1) :
    ramanujanThetaRaw q q - ramanujanThetaRaw (-q) (-q) =
      2 * q * ramanujanThetaRaw 1 (q ^ 8) := by
  have h₃ := (ramanujanTheta_entry30 q q h).2.2 hq
  rwa [div_self hq, show q ^ 5 * q ^ 3 = q ^ 8 by ring] at h₃

-- At `a = 0`, where (iii) is not asserted, the even part (ii) still holds.
example (b : ℂ) :
    ramanujanThetaRaw 0 b + ramanujanThetaRaw 0 (-b) = 2 * ramanujanThetaRaw 0 0 := by
  simpa using (ramanujanTheta_entry30 0 b (by simp)).2.1

#print axioms MetaMathlibExt.ramanujanTheta_entry30
