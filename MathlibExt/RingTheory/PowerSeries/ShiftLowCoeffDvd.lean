/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_PowerSeries_dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow.lean`
and
`P2M/Sol/S_PowerSeries_dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

namespace PowerSeries

open IsLocalRing

variable {A : Type*} [CommRing A]

private theorem exists_X_add_C_pow_succ_eq_add_mul_sq (d : A) (N : ℕ) :
    ∃ R : A⟦X⟧, (X + C d) ^ (N + 1) =
      X ^ (N + 1) + C ((N + 1 : A) * d) * X ^ N + C (d ^ 2) * R := by
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ N ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨(X + C d) * R + C ((N + 1 : A)) * X ^ N, ?_⟩
    rw [pow_succ, hR]
    simp only [map_mul, map_pow, map_add, map_one, map_natCast, Nat.cast_add, Nat.cast_one]
    ring

private theorem exists_coeff_eq_of_smul_eq_mul_X_add_C_pow_sub_X_pow
    {N : ℕ} {d e : A} {u F : A⟦X⟧}
    (hF : e • F = u * (X + C d) ^ (N + 1) - X ^ (N + 1)) :
    ∃ R : A⟦X⟧,
      (∀ j, j + 1 ≤ N → e * coeff j F = d ^ 2 * coeff j (u * R)) ∧
      e * coeff N F = d * ((N + 1 : A) * constantCoeff u + d * coeff N (u * R)) ∧
      e * coeff (N + 1) F =
        (constantCoeff u - 1) + d * ((N + 1 : A) * coeff 1 u + d * coeff (N + 1) (u * R)) := by
  obtain ⟨R, hR⟩ := exists_X_add_C_pow_succ_eq_add_mul_sq d N
  have hP : u * (X + C d) ^ (N + 1) - X ^ (N + 1) =
      (u - 1) * X ^ (N + 1) + C ((N + 1 : A) * d) * (u * X ^ N) + C (d ^ 2) * (u * R) := by
    rw [hR]; ring
  have hc : ∀ i, e * coeff i F = coeff i ((u - 1) * X ^ (N + 1)) +
      (N + 1 : A) * d * coeff i (u * X ^ N) + d ^ 2 * coeff i (u * R) := by
    intro i
    have h := congr_arg (coeff i) hF
    rw [hP] at h
    simpa only [map_smul, smul_eq_mul, map_add, coeff_C_mul] using h
  refine ⟨R, ?_, ?_, ?_⟩
  · intro j hj
    have h1 : ¬ (N + 1 ≤ j) := by omega
    have h2 : ¬ (N ≤ j) := by omega
    rw [hc j]
    simp [coeff_mul_X_pow', h1, h2]
  · rw [hc N]
    simp [coeff_mul_X_pow']
    ring
  · rw [hc (N + 1)]
    simp [coeff_mul_X_pow']
    ring

/-- Divisibility of low coefficients in `e • F = u * (X + C d) ^ n - X ^ n`
over a commutative local domain.

If `n` is invertible in `A`, `d` lies in the maximal ideal, `e ≠ 0`, and
`j + 2 ≤ n`, then `d ∣ coeff j F`. No hypothesis that `u` or its constant
coefficient is a unit is needed: when the constant coefficient is not a
unit, the top coefficient relation instead shows that `e` itself is a unit
up to the factor supplied by that relation. -/
public theorem dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow
    [IsLocalRing A] [IsDomain A]
    {n : ℕ} (hn : IsUnit (n : A)) {d e : A} (hd : d ∈ maximalIdeal A) (he : e ≠ 0)
    {u F : A⟦X⟧} (hF : e • F = u * (X + C d) ^ n - X ^ n) {j : ℕ} (hj : j + 2 ≤ n) :
    d ∣ coeff j F := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  obtain ⟨R, hlow, hN, hN1⟩ := exists_coeff_eq_of_smul_eq_mul_X_add_C_pow_sub_X_pow hF
  have ej : e * coeff j F = d ^ 2 * coeff j (u * R) := hlow j (by omega)
  by_cases hu : IsUnit (constantCoeff u)
  · have hv : IsUnit ((N + 1 : A) * constantCoeff u + d * coeff N (u * R)) := by
      have h1 : IsUnit ((N + 1 : A) * constantCoeff u) := by
        have hcast : IsUnit ((N + 1 : ℕ) : A) := hn
        exact_mod_cast hcast.mul hu
      by_contra h
      have hmem : (N + 1 : A) * constantCoeff u + d * coeff N (u * R) ∈ maximalIdeal A :=
        (IsLocalRing.mem_maximalIdeal _).mpr h
      have h2 : (N + 1 : A) * constantCoeff u ∈ maximalIdeal A := by
        simpa using sub_mem hmem (Ideal.mul_mem_right (coeff N (u * R)) _ hd)
      exact h2 h1
    obtain ⟨v, hv'⟩ := hv
    rw [← hv'] at hN
    have hdw : d = e * (coeff N F * ↑v⁻¹) := by
      calc d = d * ↑v * ↑v⁻¹ := by simp
        _ = e * coeff N F * ↑v⁻¹ := by rw [hN]
        _ = e * (coeff N F * ↑v⁻¹) := by ring
    refine ⟨coeff N F * ↑v⁻¹ * coeff j (u * R), mul_left_cancel₀ he ?_⟩
    rw [ej]
    calc d ^ 2 * coeff j (u * R) = d * d * coeff j (u * R) := by ring
      _ = d * (e * (coeff N F * ↑v⁻¹)) * coeff j (u * R) := by rw [← hdw]
      _ = e * (d * (coeff N F * ↑v⁻¹ * coeff j (u * R))) := by ring
  · have hm : constantCoeff u + d * ((N + 1 : A) * coeff 1 u + d * coeff (N + 1) (u * R)) ∈
        maximalIdeal A :=
      add_mem ((IsLocalRing.mem_maximalIdeal _).mpr hu) (Ideal.mul_mem_right _ _ hd)
    have hunit : IsUnit (e * coeff (N + 1) F) := by
      rw [hN1]
      have hrewrite : constantCoeff u - 1 + d * ((N + 1 : A) * coeff 1 u +
          d * coeff (N + 1) (u * R)) =
          -(1 - (constantCoeff u + d * ((N + 1 : A) * coeff 1 u +
            d * coeff (N + 1) (u * R)))) := by
        ring
      rw [hrewrite]
      exact (isUnit_one_sub_self_of_mem_nonunits _ hm).neg
    obtain ⟨eu, heu⟩ := isUnit_of_mul_isUnit_left hunit
    refine ⟨↑eu⁻¹ * d * coeff j (u * R), ?_⟩
    calc coeff j F = ↑eu⁻¹ * (↑eu * coeff j F) := (Units.inv_mul_cancel_left _ _).symm
      _ = ↑eu⁻¹ * (d ^ 2 * coeff j (u * R)) := by rw [heu, ej]
      _ = d * (↑eu⁻¹ * d * coeff j (u * R)) := by ring

end PowerSeries
