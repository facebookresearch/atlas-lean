/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.TrinomialInverseTransform

open PowerSeries

namespace MetaMathlibExt

private noncomputable def sqrtOneAdd (p : PowerSeries ℚ) : PowerSeries ℚ :=
  (binomialSeries ℚ (1 / 2 : ℚ)).subst p

private lemma sqrtOneAdd_sq {p : PowerSeries ℚ} (hp : constantCoeff p = 0) :
    sqrtOneAdd p ^ 2 = 1 + p := by
  have hs := HasSubst.of_constantCoeff_zero' hp
  have hB : binomialSeries ℚ (1 / 2 : ℚ) ^ 2 = 1 + X := by
    rw [pow_two, ← binomialSeries_add, show (1 / 2 + 1 / 2 : ℚ) = (1 : ℕ) by norm_num,
      binomialSeries_nat, pow_one]
  rw [sqrtOneAdd, ← subst_pow hs, hB, ← coe_substAlgHom hs, map_add, map_one, substAlgHom_X]

private lemma constantCoeff_sqrtOneAdd {p : PowerSeries ℚ} (hp : constantCoeff p = 0) :
    constantCoeff (sqrtOneAdd p) = 1 := by
  simp only [sqrtOneAdd, constantCoeff_eq (subst p (binomialSeries ℚ (1 / 2 : ℚ))),
    constantCoeff_subst_of_constantCoeff_zero hp, Algebra.algebraMap_self, RingHom.id_apply,
    binomialSeries_constantCoeff]

private noncomputable def s : PowerSeries ℚ := 2 * sqrtOneAdd (-C (3 / 4) * X ^ 2)
private noncomputable def q : PowerSeries ℚ := sqrtOneAdd (-C (1 / 2) * (X ^ 2 + X * s))
private noncomputable def r : PowerSeries ℚ := sqrtOneAdd (-X + X ^ 2)

private lemma hs : s ^ 2 = 4 - 3 * X ^ 2 := by
  have hfour : (2 : PowerSeries ℚ) ^ 2 = C 4 := by
    rw [map_ofNat]
    ring
  have hscalar : C (4 : ℚ) * C (3 / 4 : ℚ) = 3 := by rw [← map_mul]; norm_num [map_ofNat]
  rw [s, mul_pow, sqrtOneAdd_sq (by simp), hfour, mul_add, mul_one, ← mul_assoc,
    mul_neg, hscalar, map_ofNat, neg_mul, sub_eq_add_neg]

private lemma hs₀ : constantCoeff s = 2 := by
  simp [s, constantCoeff_sqrtOneAdd, map_ofNat]

private lemma hq : 2 * q ^ 2 = 2 - X ^ 2 - X * s := by
  have hscalar : (2 : PowerSeries ℚ) * C (1 / 2 : ℚ) = 1 := by
    rw [← map_ofNat C 2, ← map_mul]
    norm_num
  rw [q, sqrtOneAdd_sq (by simp), mul_add, mul_one, ← mul_assoc, mul_neg, hscalar]
  ring

private lemma hq₀ : constantCoeff q = 1 := constantCoeff_sqrtOneAdd (by simp)

private lemma hr : r ^ 2 = 1 - X + X ^ 2 := by
  rw [r, sqrtOneAdd_sq (by simp)]
  ring

private lemma hr₀ : constantCoeff r = 1 := constantCoeff_sqrtOneAdd (by simp)

private noncomputable def sample : PowerSeries ℚ := C 2 + C 3 * X + C 5 * X ^ 2

private noncomputable def transformed (f : PowerSeries ℚ) : PowerSeries ℚ :=
  let α := -2 * (2 * q + X ^ 2 * s - X) * (q * (3 * X ^ 4 + 2 * X * s - X ^ 2 - 4))⁻¹
  let β := X * (X + s) * (2 * (1 - X ^ 2))⁻¹
  α * f.subst β

-- The zero row recovers the constant term without any positivity hypothesis on n.
example : coeff 0 ((2 - X) * (2 * (1 - X + X ^ 2))⁻¹ * (transformed sample).subst (X * r⁻¹)) =
    2 := by
  have h := coeff_two_mul_eq_inverse_trinomial_transform (S := s) (Q := q) (R := r)
    (hS := hs) (hS0 := hs₀) (hQ := hq) (hQ0 := hq₀) (hR := hr) (hR0 := hr₀) (f := sample) (n := 0)
  simpa [transformed, sample, coeff_zero_eq_constantCoeff] using h.symm

-- The second coefficient is recovered even with nonzero constant and linear terms.
example : coeff 2 ((2 - X) * (1 - X) ^ 2 * (2 * (1 - X + X ^ 2))⁻¹ *
    (transformed sample).subst (X * r⁻¹)) = 5 := by
  have h := coeff_two_mul_eq_inverse_trinomial_transform (S := s) (Q := q) (R := r)
    (hS := hs) (hS0 := hs₀) (hQ := hq) (hQ0 := hq₀) (hR := hr) (hR0 := hr₀) (f := sample) (n := 1)
  simpa [transformed, sample, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow] using h.symm

end MetaMathlibExt
