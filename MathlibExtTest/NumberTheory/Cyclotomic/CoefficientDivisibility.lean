/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Cyclotomic.CoefficientDivisibility

open scoped NumberField
open Finset

namespace CyclotomicCoefficientDivisibilityTest

section ExactSource

variable {p : ℕ} {L : Type*} [Field L] [CharZero L]
  [IsCyclotomicExtension {p} ℚ L]

-- Exact R521–524 type, including the last index and arbitrary zero anchor.
theorem source_last [hp : Fact p.Prime] {ζ : 𝓞 L}
    (hζ : IsPrimitiveRoot ζ p) {f : Fin p → ℤ} (hf : ∃ i, f i = 0) {m : ℤ}
    (hdiv : ↑m ∣ ∑ j, f j • ζ ^ (j : ℕ)) :
    m ∣ f ⟨p.pred, Nat.pred_lt hp.out.ne_zero⟩ :=
  hζ.int_dvd_coeff_of_dvd_sum hf hdiv _

-- Exact R568–570 type; no NumberField instance or sign constraint.
theorem source_all [Fact p.Prime] {ζ : 𝓞 L}
    (hζ : IsPrimitiveRoot ζ p) {f : Fin p → ℤ} (hf : ∃ i, f i = 0) {m : ℤ}
    (hdiv : ↑m ∣ ∑ j, f j • ζ ^ (j : ℕ)) : ∀ j, m ∣ f j :=
  hζ.int_dvd_coeff_of_dvd_sum hf hdiv

end ExactSource

section Applications

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [CharZero L]
  [IsCyclotomicExtension {p} ℚ L] {ζ : 𝓞 L}

-- Recover an integer correction vector from congruent cyclotomic sums.
theorem recover_coordinates (hζ : IsPrimitiveRoot ζ p) {f g : Fin p → ℤ}
    (hanchor : ∃ i, f i = g i) {m : ℤ}
    (hcong : (m : 𝓞 L) ∣
      (∑ j, f j • ζ ^ (j : ℕ)) - ∑ j, g j • ζ ^ (j : ℕ)) :
    ∃ c : Fin p → ℤ, ∀ j, f j = g j + m * c j := by
  have hd : (m : 𝓞 L) ∣ ∑ j, (f j - g j) • ζ ^ (j : ℕ) := by
    simpa only [sub_smul, sum_sub_distrib] using hcong
  have hz : ∃ i, f i - g i = 0 := by
    obtain ⟨i, hi⟩ := hanchor
    exact ⟨i, sub_eq_zero.mpr hi⟩
  have hc := hζ.int_dvd_coeff_of_dvd_sum hz hd
  choose c hc using hc
  refine ⟨c, fun j => ?_⟩
  rw [← hc j]
  omega

-- Two distinct powers are integrally independent if a third index is absent.
-- This uses m = 0, not cancellation by a nonzero modulus.
theorem sparse_relation (hζ : IsPrimitiveRoot ζ p) (i j k : Fin p)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a b : ℤ)
    (hrel : a • ζ ^ (i : ℕ) + b • ζ ^ (j : ℕ) = 0) : a = 0 ∧ b = 0 := by
  let f : Fin p → ℤ := fun t =>
    (if t = i then a else 0) + (if t = j then b else 0)
  have hz : ∃ t, f t = 0 := ⟨k, by simp [f, hki, hkj]⟩
  have hs : ∑ t, f t • ζ ^ (t : ℕ) = 0 := by
    simpa [f, add_smul, sum_add_distrib, ite_smul] using hrel
  have hd : ((0 : ℤ) : 𝓞 L) ∣ ∑ t, f t • ζ ^ (t : ℕ) := by
    simpa only [Int.cast_zero, zero_dvd_iff] using hs
  have hc := hζ.int_dvd_coeff_of_dvd_sum (m := 0) hz hd
  constructor
  · simpa [f, hij] using hc i
  · simpa [f, hij.symm] using hc j

end Applications

section Boundaries

local notation "K₂" => CyclotomicField 2 ℚ
local notation "K₃" => CyclotomicField 3 ℚ
local instance : IsCyclotomicExtension {2} ℚ K₂ :=
  CyclotomicField.isCyclotomicExtension 2 ℚ
local instance : IsCyclotomicExtension {3} ℚ K₃ :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
local notation "ζ₂" =>
  IsPrimitiveRoot.toInteger (IsCyclotomicExtension.zeta_spec 2 ℚ K₂)
local notation "ζ₃" =>
  IsPrimitiveRoot.toInteger (IsCyclotomicExtension.zeta_spec 3 ℚ K₃)

-- Smallest prime, non-last zero anchor, negative modulus, nonzero sum.
theorem binary_negative :
    (∑ j : Fin 2, (![0, 6] j : ℤ) • ζ₂ ^ (j : ℕ)) ≠ 0 ∧
      ∀ j : Fin 2, (-3 : ℤ) ∣ ![0, 6] j := by
  have hz := (IsCyclotomicExtension.zeta_spec 2 ℚ K₂).toInteger_isPrimitiveRoot
  have hs : (∑ j : Fin 2, (![0, 6] j : ℤ) • ζ₂ ^ (j : ℕ)) = -6 := by
    norm_num [Fin.sum_univ_two, hz.eq_neg_one_of_two_right, zsmul_eq_mul]
  have hd : ((-3 : ℤ) : 𝓞 K₂) ∣
      ∑ j : Fin 2, (![0, 6] j : ℤ) • ζ₂ ^ (j : ℕ) := by
    rw [hs]
    exact ⟨2, by norm_num⟩
  exact ⟨by rw [hs]; norm_num,
    hz.int_dvd_coeff_of_dvd_sum ⟨0, rfl⟩ hd⟩

-- Last zero anchor, prime 3, and a composite modulus dividing a nonzero sum.
theorem cubic_composite :
    (∑ j : Fin 3, (![6, -12, 0] j : ℤ) • ζ₃ ^ (j : ℕ)) ≠ 0 ∧
      ∀ j : Fin 3, (6 : ℤ) ∣ ![6, -12, 0] j := by
  have hz := (IsCyclotomicExtension.zeta_spec 3 ℚ K₃).toInteger_isPrimitiveRoot
  have hs : (∑ j : Fin 3, (![6, -12, 0] j : ℤ) • ζ₃ ^ (j : ℕ)) =
      6 - 12 * ζ₃ := by
    norm_num [Fin.sum_univ_succ, zsmul_eq_mul, sub_eq_add_neg]
  have hd : ((6 : ℤ) : 𝓞 K₃) ∣
      ∑ j : Fin 3, (![6, -12, 0] j : ℤ) • ζ₃ ^ (j : ℕ) := by
    rw [hs]
    exact ⟨1 - 2 * ζ₃, by norm_num; ring⟩
  refine ⟨?_, hz.int_dvd_coeff_of_dvd_sum ⟨2, rfl⟩ hd⟩
  intro hzero
  have hr : (6 : ℤ) • ζ₃ ^ (0 : ℕ) + (-12 : ℤ) • ζ₃ ^ (1 : ℕ) = 0 := by
    simpa [Fin.sum_univ_succ] using hzero
  have h := (sparse_relation hz 0 1 2 (by decide) (by decide)
    (by decide) 6 (-12) hr).1
  norm_num at h

-- A concrete m = 0 application: the only zero-anchored zero relation is zero.
theorem zero_modulus (f : Fin 3 → ℤ) (hf : ∃ i, f i = 0)
    (hs : ∑ j, f j • ζ₃ ^ (j : ℕ) = 0) : f = 0 := by
  have hz := (IsCyclotomicExtension.zeta_spec 3 ℚ K₃).toInteger_isPrimitiveRoot
  have hd : ((0 : ℤ) : 𝓞 K₃) ∣ ∑ j, f j • ζ₃ ^ (j : ℕ) := by
    simpa only [Int.cast_zero, zero_dvd_iff] using hs
  funext j
  simpa only [zero_dvd_iff, Pi.zero_apply] using
    hz.int_dvd_coeff_of_dvd_sum (m := 0) hf hd j

-- Satisfiability of the zero-modulus premises, separate from nonzero fixtures.
theorem zero_modulus_witness :
    ∃ f : Fin 3 → ℤ, (∃ i, f i = 0) ∧
      (∑ j, f j • ζ₃ ^ (j : ℕ)) = 0 ∧ f = 0 := by
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · simp
  · exact zero_modulus 0 ⟨0, rfl⟩ (by simp)

-- Without a zero coefficient, 2 divides the sum but not the coefficients.
-- The all-differences generalization still applies to this countermodel.
theorem excluded_zero_anchor :
    ((2 : ℤ) : 𝓞 K₃) ∣ (∑ j : Fin 3, (1 : ℤ) • ζ₃ ^ (j : ℕ)) ∧
      (¬ ∃ i : Fin 3, (fun _ : Fin 3 => (1 : ℤ)) i = 0) ∧
      (¬ ∀ j : Fin 3, (2 : ℤ) ∣ (fun _ : Fin 3 => (1 : ℤ)) j) ∧
      ∀ i j : Fin 3, (2 : ℤ) ∣
        (fun _ : Fin 3 => (1 : ℤ)) i - (fun _ : Fin 3 => (1 : ℤ)) j := by
  have hz := (IsCyclotomicExtension.zeta_spec 3 ℚ K₃).toInteger_isPrimitiveRoot
  have hs : (∑ j : Fin 3, (1 : ℤ) • ζ₃ ^ (j : ℕ)) = 0 := by
    simpa [Finset.sum_range] using hz.geom_sum_eq_zero (by decide)
  have hd : ((2 : ℤ) : 𝓞 K₃) ∣ ∑ j : Fin 3, (1 : ℤ) • ζ₃ ^ (j : ℕ) := by
    rw [hs]
    exact dvd_zero _
  refine ⟨hd, by norm_num, ?_, hz.int_dvd_coeff_sub_of_dvd_sum hd⟩
  intro h
  have hh := h 0
  norm_num at hh

-- The recovery application returns a correction vector for a non-last
-- anchor and a negative composite modulus, not only a homogeneous relation.
theorem cubic_negative_recovery :
    ∃ c : Fin 3 → ℤ, ∀ j, (![6, 0, 12] j : ℤ) = -6 * c j := by
  have hz := (IsCyclotomicExtension.zeta_spec 3 ℚ K₃).toInteger_isPrimitiveRoot
  have hd : ((-6 : ℤ) : 𝓞 K₃) ∣
      ∑ j : Fin 3, (![6, 0, 12] j : ℤ) • ζ₃ ^ (j : ℕ) := by
    refine ⟨-1 - 2 * ζ₃ ^ 2, ?_⟩
    norm_num [Fin.sum_univ_succ, zsmul_eq_mul]
    ring
  have hc := recover_coordinates hz (f := ![6, 0, 12]) (g := 0)
    ⟨1, rfl⟩ (m := -6) (by
      simpa only [Pi.zero_apply, zero_smul, sum_const_zero, sub_zero] using hd)
  simpa only [Pi.zero_apply, zero_add] using hc

end Boundaries

end CyclotomicCoefficientDivisibilityTest
