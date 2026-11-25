/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Weighted sum of an additive character

Multiplying the weighted sum by one minus the character value reduces it to a geometric sum
and a boundary term.
-/

namespace MetaMathlibExt

open Complex Finset

private lemma sum_mul_additive_character.weighted_geom_sum (z : ℂ) (n : ℕ) :
    (∑ b ∈ range n, (b : ℂ) * z ^ b) * (1 - z) =
      z * (∑ b ∈ range n, z ^ b) - n * z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, add_mul, ih, Nat.cast_succ, pow_succ]
    ring

/-- **Weighted sum of an additive character.** Let $q \ge 2$, let $k$ be a natural number not
divisible by $q$, and write $e_q(x) = e^{2\pi i x / q}$. Then
$$\sum_{b=1}^{q-1} b\, e_q(-kb) = -\frac{q}{1 - e_q(-k)}.$$

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 3. -/
public theorem sum_mul_additive_character {q k : ℕ} (hq : 2 ≤ q) (hk : ¬ q ∣ k) :
    ∑ b ∈ Icc 1 (q - 1), (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / q) =
      -q / (1 - exp (2 * Real.pi * I * (-(k : ℂ)) / q)) := by
  let z := exp (2 * Real.pi * I * (-(k : ℂ)) / q)
  have hζ := (isPrimitiveRoot_exp q (by omega : q ≠ 0)).inv
  have hz : z = (exp (2 * Real.pi * I / q))⁻¹ ^ k := by
    rw [← exp_neg, ← exp_nat_mul]
    dsimp only [z]
    congr 1
    ring
  have hne : z ≠ 1 := by
    rw [hz]
    exact mt (hζ.pow_eq_one_iff_dvd k).mp hk
  have hpow : z ^ q = 1 := by
    rw [hz, ← pow_mul, Nat.mul_comm k q, pow_mul, hζ.pow_eq_one, one_pow]
  have hphase (b : ℕ) : exp (2 * Real.pi * I * (-(k * b : ℂ)) / q) = z ^ b := by
    rw [← exp_nat_mul]
    congr 1
    ring
  change _ = -(q : ℂ) / (1 - z)
  simp_rw [hphase]
  have hq₁ : 1 ≤ q := by omega
  rw [← Ico_add_one_right_eq_Icc, Nat.sub_add_cancel hq₁, sum_Ico_eq_sub _ hq₁]
  simp only [sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  apply (eq_div_iff (sub_ne_zero.mpr hne.symm)).2
  rw [sum_mul_additive_character.weighted_geom_sum, geom_sum_eq hne, hpow]
  simp

end MetaMathlibExt
