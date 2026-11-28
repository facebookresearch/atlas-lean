/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Theorems/Thm_Rat_hilbertReciprocity_even_card_not_ternary_isotropic.lean`
and
`P2M/Sol/S_Rat_hilbertReciprocity_even_card_not_ternary_isotropic.lean`
and
`Theorems/Thm_Padic_exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two.lean`
and
`P2M/Sol/S_Padic_exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two.lean`
and
`Theorems/Thm_Padic_exists_ternary_isotropic_iff_of_norm_eq_one_two.lean`
and
`P2M/Sol/S_Padic_exists_ternary_isotropic_iff_of_norm_eq_one_two.lean`
and
`Theorems/Thm_Padic_exists_ternary_isotropic_two_mul_iff_of_norm_eq_one.lean`
and
`P2M/Sol/S_Padic_exists_ternary_isotropic_two_mul_iff_of_norm_eq_one.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import MathlibExt.NumberTheory.Padics.TernaryIsotropic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Hilbert reciprocity for ternary forms over `ℚ`
-/
@[expose] public section

namespace HilbertRecipOddPort

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

private theorem norm_lt_one_of_toZMod_eq_zero {c : ℤ_[p]} (h : PadicInt.toZMod c = 0) : ‖c‖ < 1
  := by
  have : c ∈ RingHom.ker (PadicInt.toZMod (p := p)) := h
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal] at this
  exact PadicInt.mem_nonunits.mp this

private theorem toZMod_eq_zero_of_norm_lt_one {c : ℤ_[p]} (h : ‖c‖ < 1) : PadicInt.toZMod c = 0
  := by
  have : c ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
    exact PadicInt.mem_nonunits.mpr h
  exact this

private theorem norm_eq_one_of_toZMod_ne_zero {c : ℤ_[p]} (h : PadicInt.toZMod c ≠ 0) : ‖c‖ = 1
  := by
  refine le_antisymm (PadicInt.norm_le_one c) (not_lt.mp fun hlt ↦ h ?_)
  exact toZMod_eq_zero_of_norm_lt_one hlt

private theorem exists_sq_eq_of_toZMod_eq_sq (hp2 : p ≠ 2) {c : ℤ_[p]} {s : ZMod p} (hs : s ≠ 0)
    (hcs : PadicInt.toZMod c = s ^ 2) : ∃ t : ℤ_[p], t ^ 2 = c := by
  obtain ⟨sl, hsl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) s
  have hslnorm : ‖sl‖ = 1 := norm_eq_one_of_toZMod_ne_zero (by rw [hsl]; exact hs)
  have htwo : ‖(2 : ℤ_[p])‖ = 1 := by
    have h := (PadicInt.norm_natCast_eq_one_iff (p := p) (n := 2)).mpr
      ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    simpa using h
  set F : ℤ_[p][X] := X ^ 2 - C c with hF
  have hFeval : aeval sl F = sl ^ 2 - c := by simp [hF]
  have hF'eval : aeval sl (derivative F) = 2 * sl := by
    simp [hF]; norm_num
  have hnormF' : ‖aeval sl (derivative F)‖ = 1 := by
    rw [hF'eval, norm_mul, htwo, hslnorm, one_mul]
  have hnormF : ‖aeval sl F‖ < 1 := by
    rw [hFeval]
    apply norm_lt_one_of_toZMod_eq_zero
    rw [map_sub, map_pow, hsl, hcs, sub_self]
  have hhens : ‖aeval sl F‖ < ‖aeval sl (derivative F)‖ ^ 2 := by
    rw [hnormF', one_pow]; exact hnormF
  obtain ⟨t, ht, -⟩ := hensels_lemma hhens
  refine ⟨t, ?_⟩
  have : aeval t F = t ^ 2 - c := by simp [hF]
  rw [this] at ht
  exact sub_eq_zero.mp ht

private theorem exists_primitive_zero {A B : ℚ_[p]} {z x y : ℚ_[p]} (hne : ¬ (z = 0 ∧ x = 0 ∧ y =
  0))
    (h : z ^ 2 - A * x ^ 2 - B * y ^ 2 = 0) :
    ∃ Z X Y : ℤ_[p], (‖Z‖ = 1 ∨ ‖X‖ = 1 ∨ ‖Y‖ = 1) ∧
      (Z : ℚ_[p]) ^ 2 - A * (X : ℚ_[p]) ^ 2 - B * (Y : ℚ_[p]) ^ 2 = 0 := by

  set m : ℝ := max ‖z‖ (max ‖x‖ ‖y‖) with hm
  have hmpos : 0 < m := by
    by_contra hle
    push Not at hle
    have hz : z = 0 := norm_le_zero_iff.mp ((le_max_left _ _).trans hle)
    have hx : x = 0 :=
      norm_le_zero_iff.mp (((le_max_left _ _).trans (le_max_right _ _)).trans hle)
    have hy : y = 0 :=
      norm_le_zero_iff.mp (((le_max_right _ _).trans (le_max_right _ _)).trans hle)
    exact hne ⟨hz, hx, hy⟩

  obtain ⟨c, hc, hcm⟩ : ∃ c : ℚ_[p], (c = z ∨ c = x ∨ c = y) ∧ ‖c‖ = m := by
    rcases le_total ‖z‖ (max ‖x‖ ‖y‖) with h1 | h1
    · rcases le_total ‖x‖ ‖y‖ with h2 | h2
      · exact ⟨y, Or.inr (Or.inr rfl), by rw [hm, max_eq_right h1, max_eq_right h2]⟩
      · exact ⟨x, Or.inr (Or.inl rfl), by rw [hm, max_eq_right h1, max_eq_left h2]⟩
    · exact ⟨z, Or.inl rfl, by rw [hm, max_eq_left h1]⟩
  have hc0 : c ≠ 0 := fun h0 ↦ by
    rw [h0, norm_zero] at hcm; exact lt_irrefl _ (hcm ▸ hmpos)
  have hzle : ‖z / c‖ ≤ 1 := by
    rw [norm_div, hcm, div_le_one hmpos]; exact le_max_left _ _
  have hxle : ‖x / c‖ ≤ 1 := by
    rw [norm_div, hcm, div_le_one hmpos]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hyle : ‖y / c‖ ≤ 1 := by
    rw [norm_div, hcm, div_le_one hmpos]; exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨⟨z / c, hzle⟩, ⟨x / c, hxle⟩, ⟨y / c, hyle⟩, ?_, ?_⟩
  · show ‖(z / c : ℚ_[p])‖ = 1 ∨ ‖(x / c : ℚ_[p])‖ = 1 ∨ ‖(y / c : ℚ_[p])‖ = 1
    rcases hc with rfl | rfl | rfl
    · exact Or.inl (by rw [div_self hc0, norm_one])
    · exact Or.inr (Or.inl (by rw [div_self hc0, norm_one]))
    · exact Or.inr (Or.inr (by rw [div_self hc0, norm_one]))
  · show (z / c) ^ 2 - A * (x / c) ^ 2 - B * (y / c) ^ 2 = 0
    field_simp
    linear_combination h

end HilbertRecipOddPort

open HilbertRecipOddPort in
private theorem Padic.exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : ℚ_[p]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (∃ z x y : ℚ_[p], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (p * a) * x ^ 2 - b * y ^ 2 = 0) ↔ IsSquare b := by
  have hpr : p.Prime := Fact.out
  constructor
  · rintro ⟨z, x, y, hne, h⟩
    obtain ⟨Z, X, Y, hprim, hZ⟩ := exists_primitive_zero hne h
    set A : ℤ_[p] := ⟨a, ha.le⟩ with hA
    set B : ℤ_[p] := ⟨b, hb.le⟩ with hB
    have hBn : ‖B‖ = 1 := hb
    have hAn : ‖A‖ = 1 := ha
    have hBres : PadicInt.toZMod B ≠ 0 := fun h0 ↦ by
      have := norm_lt_one_of_toZMod_eq_zero h0; rw [hBn] at this; exact lt_irrefl _ this
    have hAres : PadicInt.toZMod A ≠ 0 := fun h0 ↦ by
      have := norm_lt_one_of_toZMod_eq_zero h0; rw [hAn] at this; exact lt_irrefl _ this

    have hrel : Z ^ 2 - (p : ℤ_[p]) * A * X ^ 2 - B * Y ^ 2 = 0 := by
      apply Subtype.val_injective
      show (Z : ℚ_[p]) ^ 2 - (p : ℚ_[p]) * a * (X : ℚ_[p]) ^ 2 - b * (Y : ℚ_[p]) ^ 2 = 0
      linear_combination hZ
    have hpres : PadicInt.toZMod (p : ℤ_[p]) = 0 := by
      rw [map_natCast, ZMod.natCast_self]

    have hred : PadicInt.toZMod Z ^ 2 - PadicInt.toZMod B * PadicInt.toZMod Y ^ 2 = 0 := by
      have := congrArg PadicInt.toZMod hrel
      simpa [map_sub, map_mul, map_pow, hpres] using this
    by_cases hY : PadicInt.toZMod Y = 0
    ·
      exfalso
      have hZ0 : PadicInt.toZMod Z = 0 := by
        rw [hY] at hred; simpa using hred
      have hZlt : ‖Z‖ < 1 := norm_lt_one_of_toZMod_eq_zero hZ0
      have hYlt : ‖Y‖ < 1 := norm_lt_one_of_toZMod_eq_zero hY
      obtain ⟨Z', hZ'⟩ := (PadicInt.norm_lt_one_iff_dvd Z).mp hZlt
      obtain ⟨Y', hY'⟩ := (PadicInt.norm_lt_one_iff_dvd Y).mp hYlt
      have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hpr.ne_zero
      have hrel' : (p : ℤ_[p]) * ((p : ℤ_[p]) * Z' ^ 2 - A * X ^ 2 - (p : ℤ_[p]) * B * Y' ^ 2)
          = 0 := by
        rw [hZ', hY'] at hrel; linear_combination hrel
      have hrel'' : (p : ℤ_[p]) * Z' ^ 2 - A * X ^ 2 - (p : ℤ_[p]) * B * Y' ^ 2 = 0 :=
        (mul_eq_zero.mp hrel').resolve_left hp0
      have hX0 : PadicInt.toZMod A * PadicInt.toZMod X ^ 2 = 0 := by
        have := congrArg PadicInt.toZMod hrel''
        simpa [map_sub, map_mul, map_pow, hpres] using this
      have hX : PadicInt.toZMod X = 0 := by
        rcases mul_eq_zero.mp hX0 with h0 | h0
        · exact absurd h0 hAres
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
      have hXlt : ‖X‖ < 1 := norm_lt_one_of_toZMod_eq_zero hX
      rcases hprim with h1 | h1 | h1
      · rw [h1] at hZlt; exact lt_irrefl _ hZlt
      · rw [h1] at hXlt; exact lt_irrefl _ hXlt
      · rw [h1] at hYlt; exact lt_irrefl _ hYlt
    ·
      set s : ZMod p := PadicInt.toZMod Z * (PadicInt.toZMod Y)⁻¹ with hs
      have hBs : PadicInt.toZMod B = s ^ 2 := by
        have e : PadicInt.toZMod Z ^ 2 = PadicInt.toZMod B * PadicInt.toZMod Y ^ 2 :=
          sub_eq_zero.mp hred
        rw [hs, mul_pow, e, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hY), mul_one]
      have hs0 : s ≠ 0 := fun h0 ↦ hBres (by rw [hBs, h0]; ring)
      obtain ⟨t, ht⟩ := exists_sq_eq_of_toZMod_eq_sq hp hs0 hBs
      refine ⟨(t : ℚ_[p]), ?_⟩
      have h := congrArg (fun s : ℤ_[p] ↦ (s : ℚ_[p])) ht
      simp only [PadicInt.coe_pow, hB, Subtype.coe_mk] at h
      rw [← h]; ring
  · rintro ⟨w, hw⟩
    refine ⟨w, 0, 1, fun ⟨_, _, h1⟩ ↦ one_ne_zero h1, ?_⟩
    rw [hw]; ring

namespace HilbertRecipDyadicUnitsPort

open Polynomial HilbertRecipOddPort

private noncomputable def r : ℤ_[2] →+* ZMod 8 := PadicInt.toZModPow (p := 2) 3

private theorem r_eq_zero_iff (x : ℤ_[2]) : r x = 0 ↔ ‖x‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
  have h1 : r x = 0 ↔ x ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 3) := Iff.rfl
  rw [h1, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  norm_num

private theorem norm_two : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
  have := PadicInt.norm_p (p := 2)
  simpa using this

private theorem r_two_mul_eq_zero_iff (x : ℤ_[2]) : r (2 * x) = 0 ↔ ‖x‖ ≤ (2 : ℝ) ^ (-2 : ℤ) := by
  rw [r_eq_zero_iff, norm_mul, norm_two]
  norm_num
  constructor <;> intro h <;> linarith

private theorem r_mul_self_of_norm_eq_one {x : ℤ_[2]} (hx : ‖x‖ = 1) : r x * r x = 1 := by
  obtain ⟨y, hy⟩ := IsUnit.exists_right_inv (PadicInt.isUnit_iff.mpr hx)
  have hr : r x * r y = 1 := by rw [← map_mul, hy, map_one]
  revert hr
  generalize r x = s, r y = t
  decide +revert

private theorem r_sq_mem (x : ℤ_[2]) : r x * r x ∈ ({0, 1, 4} : Finset (ZMod 8)) := by
  generalize r x = s
  decide +revert

private theorem exists_sq_eq_of_r_eq_one {c : ℤ_[2]} (hc : r c = 1) : ∃ t : ℤ_[2], t ^ 2 = c := by
  have hc1 : ‖c - 1‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    rw [← r_eq_zero_iff, map_sub, hc, map_one, sub_self]
  set F : ℤ_[2][X] := X ^ 2 - C c with hF
  have hFeval : aeval (1 : ℤ_[2]) F = 1 - c := by simp [hF]
  have hF'eval : aeval (1 : ℤ_[2]) (derivative F) = 2 := by
    simp [hF]; norm_num
  have hhens : ‖aeval (1 : ℤ_[2]) F‖ < ‖aeval (1 : ℤ_[2]) (derivative F)‖ ^ 2 := by
    rw [hF'eval, hFeval, norm_two, norm_sub_rev]
    refine lt_of_le_of_lt hc1 ?_
    norm_num
  obtain ⟨t, ht, -⟩ := hensels_lemma hhens
  refine ⟨t, ?_⟩
  have : aeval t F = t ^ 2 - c := by simp [hF]
  rw [this] at ht
  exact sub_eq_zero.mp ht

private theorem norm_coe_sub_one (B : ℤ_[2]) : ‖B - 1‖ = ‖(B : ℚ_[2]) - 1‖ := by
  rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]

private theorem core_units : ∀ u v : ZMod 8, u * u = 1 → v * v = 1 →
    ∀ sz ∈ ({0, 1, 4} : Finset (ZMod 8)), ∀ sx ∈ ({0, 1, 4} : Finset (ZMod 8)),
    ∀ sy ∈ ({0, 1, 4} : Finset (ZMod 8)),
    (sz = 1 ∨ sx = 1 ∨ sy = 1) → sz - u * sx - v * sy = 0 →
    (2 * (u - 1) = 0 ∨ 2 * (v - 1) = 0) := by
  decide

private theorem two_mul_sub_one_eq_zero : ∀ t : ZMod 8, 2 * (t - 1) = 0 → t = 1 ∨ t = 5 := by decide

private theorem five_add_four_mul : ∀ v : ZMod 8, v * v = 1 → 5 + 4 * v = 1 := by decide

private theorem isotropic_of_norm_sub_one_le (a b : ℚ_[2]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (h : ‖a - 1‖ ≤ (2 : ℝ) ^ (-2 : ℤ)) :
    ∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 := by
  set A : ℤ_[2] := ⟨a, ha.le⟩ with hA
  set B : ℤ_[2] := ⟨b, hb.le⟩ with hB
  have hBn : ‖B‖ = 1 := hb
  have hA1 : ‖A - 1‖ ≤ (2 : ℝ) ^ (-2 : ℤ) := by rw [norm_coe_sub_one]; exact h
  have h2 : 2 * (r A - 1) = 0 := by
    have := (r_two_mul_eq_zero_iff (A - 1)).mpr hA1
    rwa [map_mul, map_sub, map_one, map_ofNat] at this
  rcases two_mul_sub_one_eq_zero _ h2 with h1 | h5
  ·
    obtain ⟨w, hw⟩ := exists_sq_eq_of_r_eq_one h1
    refine ⟨w, 1, 0, fun ⟨_, h1, _⟩ ↦ one_ne_zero h1, ?_⟩
    have : (w : ℚ_[2]) ^ 2 = a := by
      have := congrArg (fun s : ℤ_[2] ↦ (s : ℚ_[2])) hw
      simpa [hA] using this
    rw [this]; ring
  ·
    have hr : r (A + 4 * B) = 1 := by
      rw [map_add, map_mul, map_ofNat, h5]
      exact five_add_four_mul _ (r_mul_self_of_norm_eq_one hBn)
    obtain ⟨w, hw⟩ := exists_sq_eq_of_r_eq_one hr
    refine ⟨w, 1, 2, fun ⟨_, h1, _⟩ ↦ one_ne_zero h1, ?_⟩
    have : (w : ℚ_[2]) ^ 2 = a + 4 * b := by
      have := congrArg (fun s : ℤ_[2] ↦ (s : ℚ_[2])) hw
      simp [hA, hB] at this
      exact this
    rw [this]; ring

private theorem units_iff (a b : ℚ_[2]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0) ↔
      ‖a - 1‖ ≤ (2 : ℝ) ^ (-2 : ℤ) ∨ ‖b - 1‖ ≤ (2 : ℝ) ^ (-2 : ℤ) := by
  constructor
  · rintro ⟨z, x, y, hne, h⟩
    obtain ⟨Z, X, Y, hprim, hZ⟩ := exists_primitive_zero hne h
    set A : ℤ_[2] := ⟨a, ha.le⟩ with hA
    set B : ℤ_[2] := ⟨b, hb.le⟩ with hB
    have hBn : ‖B‖ = 1 := hb
    have hAn : ‖A‖ = 1 := ha
    have hrel : Z ^ 2 - A * X ^ 2 - B * Y ^ 2 = 0 := by
      apply Subtype.val_injective
      show (Z : ℚ_[2]) ^ 2 - a * (X : ℚ_[2]) ^ 2 - b * (Y : ℚ_[2]) ^ 2 = 0
      linear_combination hZ
    have hred : r Z * r Z - r A * (r X * r X) - r B * (r Y * r Y) = 0 := by
      have := congrArg r hrel
      simpa [map_sub, map_mul, map_pow, sq] using this
    have hprim' : r Z * r Z = 1 ∨ r X * r X = 1 ∨ r Y * r Y = 1 := by
      rcases hprim with h1 | h1 | h1
      · exact Or.inl (r_mul_self_of_norm_eq_one h1)
      · exact Or.inr (Or.inl (r_mul_self_of_norm_eq_one h1))
      · exact Or.inr (Or.inr (r_mul_self_of_norm_eq_one h1))
    have hcore := core_units (r A) (r B) (r_mul_self_of_norm_eq_one hAn)
      (r_mul_self_of_norm_eq_one hBn) _ (r_sq_mem Z) _ (r_sq_mem X) _ (r_sq_mem Y) hprim' hred
    rcases hcore with h1 | h1
    · left
      have : r (2 * (A - 1)) = 0 := by rwa [map_mul, map_sub, map_one, map_ofNat]
      have := (r_two_mul_eq_zero_iff _).mp this
      rwa [norm_coe_sub_one] at this
    · right
      have : r (2 * (B - 1)) = 0 := by rwa [map_mul, map_sub, map_one, map_ofNat]
      have := (r_two_mul_eq_zero_iff _).mp this
      rwa [norm_coe_sub_one] at this
  · rintro (h | h)
    · exact isotropic_of_norm_sub_one_le a b ha hb h
    · obtain ⟨z, x, y, hne, hz⟩ := isotropic_of_norm_sub_one_le b a hb ha h
      refine ⟨z, y, x, fun ⟨h1, h2, h3⟩ ↦ hne ⟨h1, h3, h2⟩, ?_⟩
      linear_combination hz

end HilbertRecipDyadicUnitsPort

namespace HilbertRecipDyadicTwoMulPort

open Polynomial HilbertRecipOddPort HilbertRecipDyadicUnitsPort

private theorem core_two_mul : ∀ u v : ZMod 8, u * u = 1 → v * v = 1 →
    ∀ sz ∈ ({0, 1, 4} : Finset (ZMod 8)), ∀ sx ∈ ({0, 1, 4} : Finset (ZMod 8)),
    ∀ sy ∈ ({0, 1, 4} : Finset (ZMod 8)),
    (sz = 1 ∨ sx = 1 ∨ sy = 1) → sz - 2 * u * sx - v * sy = 0 →
    (v = 1 ∨ 2 * u + v - 1 = 0) := by
  decide

private theorem two_mul_iff (a b : ℚ_[2]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (2 * a) * x ^ 2 - b * y ^ 2 = 0) ↔
      ‖b - 1‖ ≤ (2 : ℝ) ^ (-3 : ℤ) ∨ ‖2 * a + b - 1‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
  set A : ℤ_[2] := ⟨a, ha.le⟩ with hA
  set B : ℤ_[2] := ⟨b, hb.le⟩ with hB
  have hBn : ‖B‖ = 1 := hb
  have hAn : ‖A‖ = 1 := ha
  have hnB : ‖B - 1‖ = ‖b - 1‖ := norm_coe_sub_one B
  have hnAB : ‖2 * A + B - 1‖ = ‖2 * a + b - 1‖ := by
    rw [PadicInt.norm_def]; push_cast [hA, hB]; rfl
  constructor
  · rintro ⟨z, x, y, hne, h⟩
    obtain ⟨Z, X, Y, hprim, hZ⟩ := exists_primitive_zero hne h
    have hrel : Z ^ 2 - 2 * A * X ^ 2 - B * Y ^ 2 = 0 := by
      apply Subtype.val_injective
      show (Z : ℚ_[2]) ^ 2 - 2 * a * (X : ℚ_[2]) ^ 2 - b * (Y : ℚ_[2]) ^ 2 = 0
      linear_combination hZ
    have hred : r Z * r Z - 2 * r A * (r X * r X) - r B * (r Y * r Y) = 0 := by
      have := congrArg r hrel
      simpa [map_sub, map_mul, map_pow, sq, map_ofNat] using this
    have hprim' : r Z * r Z = 1 ∨ r X * r X = 1 ∨ r Y * r Y = 1 := by
      rcases hprim with h1 | h1 | h1
      · exact Or.inl (r_mul_self_of_norm_eq_one h1)
      · exact Or.inr (Or.inl (r_mul_self_of_norm_eq_one h1))
      · exact Or.inr (Or.inr (r_mul_self_of_norm_eq_one h1))
    have hcore := core_two_mul (r A) (r B) (r_mul_self_of_norm_eq_one hAn)
      (r_mul_self_of_norm_eq_one hBn) _ (r_sq_mem Z) _ (r_sq_mem X) _ (r_sq_mem Y) hprim' hred
    rcases hcore with h1 | h1
    · left
      have : r (B - 1) = 0 := by rw [map_sub, map_one, h1, sub_self]
      rw [← hnB]; exact (r_eq_zero_iff _).mp this
    · right
      have : r (2 * A + B - 1) = 0 := by
        rwa [map_sub, map_add, map_mul, map_one, map_ofNat]
      rw [← hnAB]; exact (r_eq_zero_iff _).mp this
  · rintro (h | h)
    · have h1 : r B = 1 := by
        rw [← hnB, ← r_eq_zero_iff, map_sub, map_one, sub_eq_zero] at h; exact h
      obtain ⟨w, hw⟩ := exists_sq_eq_of_r_eq_one h1
      refine ⟨w, 0, 1, fun ⟨_, _, h1⟩ ↦ one_ne_zero h1, ?_⟩
      have : (w : ℚ_[2]) ^ 2 = b := by
        have := congrArg (fun s : ℤ_[2] ↦ (s : ℚ_[2])) hw
        simpa [hB] using this
      rw [this]; ring
    · have h1 : r (2 * A + B) = 1 := by
        rw [← hnAB, ← r_eq_zero_iff, map_sub, map_one, sub_eq_zero] at h; exact h
      obtain ⟨w, hw⟩ := exists_sq_eq_of_r_eq_one h1
      refine ⟨w, 1, 1, fun ⟨_, h1, _⟩ ↦ one_ne_zero h1, ?_⟩
      have : (w : ℚ_[2]) ^ 2 = 2 * a + b := by
        have := congrArg (fun s : ℤ_[2] ↦ (s : ℚ_[2])) hw
        simp [hA, hB] at this
        exact this
      rw [this]; ring

end HilbertRecipDyadicTwoMulPort

open ZMod NumberTheorySymbols

namespace HilbertRecipPort

private def Iso {F : Type*} [Field F] (A B : F) : Prop :=
  ∃ z x y : F, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - A * x ^ 2 - B * y ^ 2 = 0

section FieldGeneric
variable {F : Type*} [Field F]

private theorem iso_symm {A B : F} (h : Iso A B) : Iso B A := by
  obtain ⟨z, x, y, hnt, heq⟩ := h
  exact ⟨z, y, x, by tauto, by linear_combination heq⟩

private theorem iso_comm {A B : F} : Iso A B ↔ Iso B A := ⟨iso_symm, iso_symm⟩

private theorem iso_mul_sq_left {A B s : F} (hs : s ≠ 0) : Iso (A * s ^ 2) B ↔ Iso A B := by
  constructor
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨z, s * x, y, ?_, by linear_combination heq⟩
    rintro ⟨hz, hx, hy⟩
    exact hnt ⟨hz, (mul_eq_zero.mp hx).resolve_left hs, hy⟩
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨s * z, x, s * y, ?_, by linear_combination s ^ 2 * heq⟩
    rintro ⟨hz, hx, hy⟩
    exact hnt ⟨(mul_eq_zero.mp hz).resolve_left hs, hx, (mul_eq_zero.mp hy).resolve_left hs⟩

private theorem iso_mul_sq_right {A B s : F} (hs : s ≠ 0) : Iso A (B * s ^ 2) ↔ Iso A B := by
  rw [iso_comm, iso_mul_sq_left hs, iso_comm]

private theorem iso_neg_mul {A B : F} (hA : A ≠ 0) : Iso A (-(A * B)) ↔ Iso A B := by
  constructor
  · rintro ⟨z, x, y, hnt, heq⟩

    refine ⟨A * x, z, A * y, ?_, by linear_combination (-A) * heq⟩
    rintro ⟨hx, hz, hy⟩
    exact hnt ⟨hz, (mul_eq_zero.mp hx).resolve_left hA, (mul_eq_zero.mp hy).resolve_left hA⟩
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨A * x, z, y, ?_, by linear_combination (-A) * heq⟩
    rintro ⟨hx, hz, hy⟩
    exact hnt ⟨hz, (mul_eq_zero.mp hx).resolve_left hA, hy⟩

end FieldGeneric

private noncomputable def ord (p : ℕ) (a : ℤ) : ℕ := padicValInt p a

private noncomputable def unt (p : ℕ) (a : ℤ) : ℤ := a / (p : ℤ) ^ padicValInt p a

private theorem decomp {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : a ≠ 0) :
    a = (p : ℤ) ^ ord p a * unt p a ∧ ¬ (p : ℤ) ∣ unt p a := by
  haveI := Fact.mk hp
  have hdvd : (p : ℤ) ^ ord p a ∣ a := padicValInt_dvd a
  have hea : a = (p : ℤ) ^ ord p a * unt p a := by
    unfold unt ord; exact (Int.mul_ediv_cancel' hdvd).symm
  refine ⟨hea, fun h ↦ ?_⟩
  have : (p : ℤ) ^ (ord p a + 1) ∣ a := by
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [pow_succ, mul_assoc, ← hc]; exact hea⟩
  rw [padicValInt_dvd_iff] at this
  rcases this with h0 | h1
  · exact ha h0
  · unfold ord at h1; omega

private theorem ord_unt_eq {p : ℕ} (hp : p.Prime) {a u : ℤ} {k : ℕ} (hu : ¬ (p : ℤ) ∣ u)
    (h : a = (p : ℤ) ^ k * u) : ord p a = k ∧ unt p a = u := by
  haveI := Fact.mk hp
  have hu0 : u ≠ 0 := fun h0 ↦ hu (h0 ▸ dvd_zero _)
  have hpk : (p : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hord : ord p a = k := by
    unfold ord
    rw [h, padicValInt.mul hpk hu0, padicValInt.eq_zero_of_not_dvd hu, add_zero]
    simp [padicValInt]
  refine ⟨hord, ?_⟩
  unfold unt
  rw [show padicValInt p a = k from hord, h, Int.mul_ediv_cancel_left _ hpk]

private theorem ord_unt_mul {p : ℕ} (hp : p.Prime) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ord p (a * b) = ord p a + ord p b ∧ unt p (a * b) = unt p a * unt p b := by
  obtain ⟨hea, hua⟩ := decomp hp ha
  obtain ⟨heb, hub⟩ := decomp hp hb
  have key : a * b = (p : ℤ) ^ (ord p a + ord p b) * (unt p a * unt p b) := by
    calc a * b = ((p : ℤ) ^ ord p a * unt p a) * ((p : ℤ) ^ ord p b * unt p b) := by
          rw [← hea, ← heb]
      _ = _ := by ring
  refine ord_unt_eq hp (fun h ↦ ?_) key
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpp.dvd_or_dvd h with h | h
  · exact hua h
  · exact hub h

private theorem unt_odd {a : ℤ} (ha : a ≠ 0) : ¬ (2 : ℤ) ∣ unt 2 a := by
  simpa using (decomp Nat.prime_two ha).2

private def sgn4 (u v : ℤ) : ℤ := if χ₄ v = -1 then χ₄ u else 1

private noncomputable def symOdd (p : ℕ) (a b : ℤ) : ℤ :=
  χ₄ p ^ (ord p a * ord p b) * J(unt p a | p) ^ ord p b * J(unt p b | p) ^ ord p a

private noncomputable def symTwo (a b : ℤ) : ℤ :=
  sgn4 (unt 2 a) (unt 2 b) * χ₈ (unt 2 a) ^ ord 2 b * χ₈ (unt 2 b) ^ ord 2 a

private noncomputable def sym (p : ℕ) (a b : ℤ) : ℤ := if p = 2 then symTwo a b else symOdd p a b

private def sgnInf (a b : ℤ) : ℤ := if a < 0 ∧ b < 0 then -1 else 1

private def IsSign (x : ℤ) : Prop := x = 1 ∨ x = -1

private theorem IsSign.mul {x y : ℤ} (hx : IsSign x) (hy : IsSign y) : IsSign (x * y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [IsSign]

private theorem IsSign.pow {x : ℤ} (hx : IsSign x) (n : ℕ) : IsSign (x ^ n) := by
  rcases hx with rfl | rfl
  · simp [IsSign]
  · rcases neg_one_pow_eq_or ℤ n with h | h <;> simp [IsSign, h]

private theorem IsSign.pow_eq_pow_mod_two {x : ℤ} (hx : IsSign x) (n : ℕ) : x ^ n = x ^ (n % 2)
  := by
  rcases hx with rfl | rfl
  · simp
  · nth_rw 1 [← Nat.div_add_mod n 2]; rw [pow_add, pow_mul]; simp

private theorem isSign_one : IsSign 1 := Or.inl rfl

private theorem χ₄_isSign_of_odd {u : ℤ} (hu : ¬ (2 : ℤ) ∣ u) : IsSign (χ₄ u) := by
  rw [χ₄_int_eq_if_mod_four]
  have : u % 2 ≠ 0 := fun h ↦ hu (Int.dvd_of_emod_eq_zero h)
  simp only [this, ite_false]
  split_ifs <;> simp [IsSign]

private theorem χ₈_isSign_of_odd {u : ℤ} (hu : ¬ (2 : ℤ) ∣ u) : IsSign (χ₈ u) := by
  rw [χ₈_int_eq_if_mod_eight]
  have : u % 2 ≠ 0 := fun h ↦ hu (Int.dvd_of_emod_eq_zero h)
  simp only [this, ite_false]
  split_ifs <;> simp [IsSign]

private theorem χ₄_nat_isSign_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : IsSign (χ₄ (p :
  ℤ)) := by
  apply χ₄_isSign_of_odd
  intro h
  have : (2 : ℕ) ∣ p := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm

private theorem jacobiSym_isSign {p : ℕ} (hp : p.Prime) {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    IsSign (J(u | p)) := by
  apply jacobiSym.eq_one_or_neg_one
  have : ¬ p ∣ u.natAbs := fun h ↦ hu (Int.natCast_dvd.mpr h)
  rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
  exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr this))

private theorem sgn4_isSign {u v : ℤ} (hu : ¬ (2 : ℤ) ∣ u) : IsSign (sgn4 u v) := by
  unfold sgn4; split_ifs
  · exact χ₄_isSign_of_odd hu
  · exact isSign_one

private theorem sym_isSign {p : ℕ} (hp : p.Prime) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsSign (sym p a b) := by
  unfold sym symOdd symTwo
  split_ifs with h2
  · exact ((sgn4_isSign (unt_odd ha)).mul ((χ₈_isSign_of_odd (unt_odd ha)).pow _)).mul
      ((χ₈_isSign_of_odd (unt_odd hb)).pow _)
  · have h4 : IsSign (χ₄ (p : ℤ)) := χ₄_nat_isSign_of_ne_two hp h2
    exact ((h4.pow _).mul ((jacobiSym_isSign hp (decomp hp ha).2).pow _)).mul
      ((jacobiSym_isSign hp (decomp hp hb).2).pow _)

private theorem sgn4_mul_left (u u' v : ℤ) : sgn4 (u * u') v = sgn4 u v * sgn4 u' v := by
  unfold sgn4; split_ifs <;> simp [Int.cast_mul, map_mul]

private theorem sgn4_comm {u v : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hv : ¬ (2 : ℤ) ∣ v) : sgn4 u v = sgn4 v
  u := by
  unfold sgn4
  rcases χ₄_isSign_of_odd hu with h | h <;> rcases χ₄_isSign_of_odd hv with h' | h' <;>
    simp [h, h']

private theorem sym_mul_left {p : ℕ} (hp : p.Prime) {a a' : ℤ} (ha : a ≠ 0) (ha' : a' ≠ 0) (b : ℤ) :
    sym p (a * a') b = sym p a b * sym p a' b := by
  obtain ⟨ho, hu⟩ := ord_unt_mul hp ha ha'
  unfold sym symOdd symTwo
  split_ifs with h2
  · subst h2
    rw [ho, hu, sgn4_mul_left, Int.cast_mul, map_mul, mul_pow, pow_add]; ring
  · rw [ho, hu, jacobiSym.mul_left, mul_pow, pow_add, add_mul, pow_add]; ring

private theorem sym_comm (p : ℕ) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    sym p a b = sym p b a := by
  unfold sym symOdd symTwo
  split_ifs with h2
  · rw [sgn4_comm (unt_odd ha) (unt_odd hb)]; ring
  · ring

private theorem sym_eq_one_of_not_dvd {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (h : ¬ (p : ℤ) ∣ 2 * a * b) : sym p a b = 1 := by
  have h2 : p ≠ 2 := by rintro rfl; exact h ⟨a * b, by ring⟩
  have ha : ¬ (p : ℤ) ∣ a := fun d ↦ h (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right d _) _)
  have hb : ¬ (p : ℤ) ∣ b := fun d ↦ h (dvd_mul_of_dvd_right d _)
  have hoa : ord p a = 0 := (ord_unt_eq hp ha (by ring : a = (p:ℤ) ^ 0 * a)).1
  have hob : ord p b = 0 := (ord_unt_eq hp hb (by ring : b = (p:ℤ) ^ 0 * b)).1
  unfold sym symOdd
  rw [ite_eq_right h2, hoa, hob]; simp

private theorem sgnInf_mul_left {a a' : ℤ} (ha : a ≠ 0) (ha' : a' ≠ 0) (b : ℤ) :
    sgnInf (a * a') b = sgnInf a b * sgnInf a' b := by
  unfold sgnInf
  rcases lt_or_gt_of_ne ha with h | h <;> rcases lt_or_gt_of_ne ha' with h' | h' <;>
    rcases lt_or_ge b 0 with hb | hb
  all_goals simp [h, h', hb, mul_neg_iff, not_lt.mpr, h.le, h'.le]

private theorem sgnInf_comm (a b : ℤ) : sgnInf a b = sgnInf b a := by
  unfold sgnInf; simp only [and_comm]

end HilbertRecipPort

namespace HilbertRecipPort

private def PF (a b : ℤ) : Prop :=
  ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * a * b → p ∈ s) →
    ∏ p ∈ s, sym p a b = sgnInf a b

private theorem prod_indep (a b : ℤ) (s t : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (_ht : ∀ p ∈ t, p.Prime)
    (htc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * a * b → p ∈ t) :
    ∏ p ∈ s ∩ t, sym p a b = ∏ p ∈ s, sym p a b := by
  apply Finset.prod_subset Finset.inter_subset_left
  intro p hps hpn
  have hpt : p ∉ t := fun h ↦ hpn (Finset.mem_inter.mpr ⟨hps, h⟩)
  exact sym_eq_one_of_not_dvd (hs p hps) (fun h ↦ hpt (htc p (hs p hps) h))

private theorem pf_of_one {a b : ℤ} (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime)
    (htc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * a * b → p ∈ t)
    (hprod : ∏ p ∈ t, sym p a b = sgnInf a b) : PF a b := by
  intro s hs hsc
  rw [← prod_indep a b s t hs ht htc, Finset.inter_comm, prod_indep a b t s ht hs hsc, hprod]

private theorem pf_symm {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (h : PF a b) : PF b a := by
  intro s hs hsc
  rw [sgnInf_comm, ← h s hs (fun p hp hd ↦ hsc p hp (by rw [mul_right_comm]; exact hd))]
  exact Finset.prod_congr rfl (fun p hp ↦ sym_comm p hb ha)

private theorem pf_mul_left {a a' b : ℤ} (ha : a ≠ 0) (ha' : a' ≠ 0) (h : PF a b)
    (h' : PF a' b) : PF (a * a') b := by
  intro s hs hsc
  rw [sgnInf_mul_left ha ha', ← h s hs (fun p hp hd ↦ hsc p hp ?_),
    ← h' s hs (fun p hp hd ↦ hsc p hp ?_), ← Finset.prod_mul_distrib]
  · exact Finset.prod_congr rfl (fun p hp ↦ sym_mul_left (hs p hp) ha ha' b)
  · exact (Dvd.dvd.mul_left hd a).trans (dvd_of_eq (by ring))
  · exact (Dvd.dvd.mul_left hd a').trans (dvd_of_eq (by ring))

private theorem pf_mul_right {a b b' : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) (h : PF a b)
    (h' : PF a b') : PF a (b * b') :=
  pf_symm (mul_ne_zero hb hb') ha (pf_mul_left hb hb' (pf_symm ha hb h) (pf_symm ha hb' h'))

private theorem not_natCast_dvd_one {p : ℕ} (hp : p.Prime) : ¬ (p : ℤ) ∣ 1 := fun h ↦
  hp.ne_one (Nat.dvd_one.mp (by simpa using Int.natCast_dvd.mp h))

private theorem not_natCast_dvd_neg_one {p : ℕ} (hp : p.Prime) : ¬ (p : ℤ) ∣ -1 := fun h ↦
  not_natCast_dvd_one hp ((dvd_neg).mp h)

private theorem not_natCast_dvd_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ (p : ℤ) ∣ q := fun h ↦
  hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (Int.natCast_dvd_natCast.mp h))

private theorem ou_one {p : ℕ} (hp : p.Prime) : ord p 1 = 0 ∧ unt p 1 = 1 :=
  ord_unt_eq hp (not_natCast_dvd_one hp) (by ring)

private theorem ou_neg_one {p : ℕ} (hp : p.Prime) : ord p (-1) = 0 ∧ unt p (-1) = -1 :=
  ord_unt_eq hp (not_natCast_dvd_neg_one hp) (by ring)

private theorem ou_self {p : ℕ} (hp : p.Prime) : ord p p = 1 ∧ unt p p = 1 :=
  ord_unt_eq hp (not_natCast_dvd_one hp) (by ring)

private theorem ou_other {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ord p q = 0 ∧ unt p q = q :=
  ord_unt_eq hp (not_natCast_dvd_prime hp hq hpq) (by ring)

private theorem chi4_neg_one : χ₄ ((-1 : ℤ) : ZMod 4) = -1 := by
  rw [Int.cast_neg, Int.cast_one]; decide
private theorem chi8_one : χ₈ ((1 : ℤ) : ZMod 8) = 1 := by simp
private theorem chi8_neg_one : χ₈ ((-1 : ℤ) : ZMod 8) = 1 := by
  rw [Int.cast_neg, Int.cast_one]; decide

private theorem sgn4_one_left (v : ℤ) : sgn4 1 v = 1 := by unfold sgn4; simp
private theorem sgn4_one_right (u : ℤ) : sgn4 u 1 = 1 := by unfold sgn4; simp
private theorem sgn4_neg_one_neg_one : sgn4 (-1) (-1) = -1 := by
  unfold sgn4; rw [chi4_neg_one]; simp
private theorem sgn4_neg_one_left {v : ℤ} (hv : ¬ (2 : ℤ) ∣ v) : sgn4 (-1) v = χ₄ v := by
  unfold sgn4; rw [chi4_neg_one]
  rcases χ₄_isSign_of_odd hv with h | h <;> simp [h]
private theorem sgn4_self_mul {u : ℤ} (hu : ¬ (2 : ℤ) ∣ u) : sgn4 u u * χ₄ u = 1 := by
  unfold sgn4
  rcases χ₄_isSign_of_odd hu with h | h <;> simp [h]

private theorem odd_of_prime_ne_two {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : ¬ (2 : ℤ) ∣ (q : ℤ) :=
  not_natCast_dvd_prime Nat.prime_two hq (Ne.symm hq2)

private theorem χ₄_nat_isSign {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : IsSign (χ₄ (q : ZMod 4)) := by
  have := χ₄_isSign_of_odd (odd_of_prime_ne_two hq hq2)
  rwa [Int.cast_natCast] at this

private theorem χ₈_nat_isSign {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : IsSign (χ₈ (q : ZMod 8)) := by
  have := χ₈_isSign_of_odd (odd_of_prime_ne_two hq hq2)
  rwa [Int.cast_natCast] at this

private theorem cover_aux {p m n : ℕ} (hp : p.Prime) (hm : m = 1 ∨ m.Prime) (hn : n = 1 ∨ n.Prime)
    (h : p ∣ 2 * m * n) : p = 2 ∨ p = m ∨ p = n := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · rcases hm with rfl | hm
      · exact absurd (Nat.dvd_one.mp h) hp.ne_one
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hm).mp h))
  · rcases hn with rfl | hn
    · exact absurd (Nat.dvd_one.mp h) hp.ne_one
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hn).mp h))

private theorem cover_int {p : ℕ} {x y : ℤ} (h : (p : ℤ) ∣ 2 * x * y) :
    p ∣ 2 * x.natAbs * y.natAbs := by
  have := Int.natCast_dvd.mp h
  simpa [Int.natAbs_mul] using this

private theorem pf_one_left (b : ℤ) : PF 1 b := by
  intro s hs _
  unfold sgnInf
  rw [ite_eq_right (by omega), Finset.prod_eq_one]
  intro p hp
  have hp' := hs p hp
  unfold sym symOdd symTwo
  rw [(ou_one hp').1, (ou_one hp').2, (ou_one Nat.prime_two).1, (ou_one Nat.prime_two).2]
  simp [sgn4_one_left, jacobiSym.one_left]

private theorem pf_neg_one_neg_one : PF (-1) (-1) := by
  refine pf_of_one {2} (by simp [Nat.prime_two]) (fun p hp hd ↦ ?_) ?_
  · have := cover_aux hp (Or.inl rfl) (Or.inl rfl) (by simpa using cover_int hd)
    rcases this with rfl | rfl | rfl <;> first | exact absurd hp Nat.not_prime_one | simp
  · rw [Finset.prod_singleton]
    unfold sym symTwo sgnInf
    rw [ite_eq_left rfl, (ou_neg_one Nat.prime_two).1, (ou_neg_one Nat.prime_two).2,
      sgn4_neg_one_neg_one]
    simp

private theorem pf_neg_one_two : PF (-1) 2 := by
  refine pf_of_one {2} (by simp [Nat.prime_two]) (fun p hp hd ↦ ?_) ?_
  · have := cover_aux hp (Or.inl rfl) (Or.inr Nat.prime_two) (by simpa using cover_int hd)
    rcases this with rfl | rfl | rfl <;> first | exact absurd hp Nat.not_prime_one | simp
  · rw [Finset.prod_singleton]
    unfold sym symTwo sgnInf
    have h2 := ou_self Nat.prime_two
    push_cast at h2
    rw [ite_eq_left rfl, (ou_neg_one Nat.prime_two).1, (ou_neg_one Nat.prime_two).2, h2.1, h2.2,
      sgn4_one_right, chi8_neg_one]
    simp

private theorem pf_neg_one_prime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : PF (-1) q := by
  have hqodd := odd_of_prime_ne_two hq hq2
  refine pf_of_one {2, q} ?_ (fun p hp hd ↦ ?_) ?_
  · simp [Nat.prime_two, hq]
  · have := cover_aux hp (Or.inl rfl) (Or.inr hq) (by simpa using cover_int hd)
    rcases this with rfl | rfl | rfl <;> first | exact absurd hp Nat.not_prime_one | simp
  · rw [Finset.prod_pair (Ne.symm hq2)]
    unfold sym symTwo symOdd sgnInf
    rw [ite_eq_left rfl, ite_eq_right hq2, (ou_neg_one Nat.prime_two).1,
      (ou_neg_one Nat.prime_two).2, (ou_other Nat.prime_two hq (Ne.symm hq2)).1,
      (ou_other Nat.prime_two hq (Ne.symm hq2)).2,
      (ou_neg_one hq).1, (ou_neg_one hq).2, (ou_self hq).1, (ou_self hq).2,
      sgn4_neg_one_left hqodd, jacobiSym.at_neg_one (hq.odd_of_ne_two hq2)]
    simp only [pow_zero, mul_one, pow_one, one_mul, jacobiSym.one_left, Int.cast_natCast]
    rw [ite_eq_right (by omega)]
    rcases χ₄_nat_isSign hq hq2 with h | h <;> rw [h] <;> norm_num

private theorem pf_two_two : PF 2 2 := by
  refine pf_of_one {2} (by simp [Nat.prime_two]) (fun p hp hd ↦ ?_) ?_
  · have := cover_aux hp (Or.inr Nat.prime_two) (Or.inr Nat.prime_two)
      (by simpa using cover_int hd)
    rcases this with rfl | rfl | rfl <;> simp
  · rw [Finset.prod_singleton]
    unfold sym symTwo sgnInf
    have h2 := ou_self Nat.prime_two
    push_cast at h2
    rw [ite_eq_left rfl, h2.1, h2.2, sgn4_one_right, chi8_one]
    simp

private theorem pf_prime_self {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : PF q q := by
  have hqodd := odd_of_prime_ne_two hq hq2
  refine pf_of_one {2, q} ?_ (fun p hp hd ↦ ?_) ?_
  · simp [Nat.prime_two, hq]
  · have := cover_aux hp (Or.inr hq) (Or.inr hq) (by simpa using cover_int hd)
    rcases this with rfl | rfl | rfl <;> first | exact absurd hp Nat.not_prime_one | simp
  · rw [Finset.prod_pair (Ne.symm hq2)]
    unfold sym symTwo symOdd sgnInf
    rw [ite_eq_left rfl, ite_eq_right hq2,
      (ou_other Nat.prime_two hq (Ne.symm hq2)).1, (ou_other Nat.prime_two hq (Ne.symm hq2)).2,
      (ou_self hq).1, (ou_self hq).2]
    simp only [pow_zero, mul_one, pow_one, jacobiSym.one_left]
    rw [ite_eq_right (by omega)]
    have := sgn4_self_mul hqodd
    rwa [Int.cast_natCast] at this

private theorem pf_two_prime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : PF 2 q := by
  have hqodd := odd_of_prime_ne_two hq hq2
  refine pf_of_one {2, q} ?_ (fun p hp hd ↦ ?_) ?_
  · simp [Nat.prime_two, hq]
  · have := cover_aux hp (Or.inr Nat.prime_two) (Or.inr hq) (by simpa using cover_int hd)
    rcases this with rfl | rfl | rfl <;> first | exact absurd hp Nat.not_prime_one | simp
  · rw [Finset.prod_pair (Ne.symm hq2)]
    unfold sym symTwo symOdd sgnInf
    have h2 := ou_self Nat.prime_two
    push_cast at h2
    rw [ite_eq_left rfl, ite_eq_right hq2, h2.1, h2.2,
      (ou_other Nat.prime_two hq (Ne.symm hq2)).1, (ou_other Nat.prime_two hq (Ne.symm hq2)).2,
      (ou_self hq).1, (ou_self hq).2]
    have h2' := ou_other hq Nat.prime_two hq2
    push_cast at h2'
    rw [h2'.1, h2'.2, sgn4_one_left]
    simp only [pow_zero, mul_one, pow_one, jacobiSym.one_left, one_mul]
    rw [ite_eq_right (by omega), jacobiSym.at_two (hq.odd_of_ne_two hq2), Int.cast_natCast]
    rcases χ₈_nat_isSign hq hq2 with h | h <;> rw [h] <;> norm_num

private theorem pf_prime_prime {q q' : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq' : q'.Prime) (hq2' :
  q' ≠ 2)
    (hqq : q ≠ q') : PF q q' := by
  have hqodd := odd_of_prime_ne_two hq hq2
  have hqodd' := odd_of_prime_ne_two hq' hq2'
  refine pf_of_one {2, q, q'} ?_ (fun p hp hd ↦ ?_) ?_
  · simp [Nat.prime_two, hq, hq']
  · have := cover_aux hp (Or.inr hq) (Or.inr hq') (by simpa using cover_int hd)
    rcases this with rfl | rfl | rfl <;> first | exact absurd hp Nat.not_prime_one | simp
  · rw [Finset.prod_insert (by simp [Ne.symm hq2, Ne.symm hq2']), Finset.prod_pair hqq]
    unfold sym symTwo symOdd sgnInf
    rw [ite_eq_left rfl, ite_eq_right hq2, ite_eq_right hq2',
      (ou_other Nat.prime_two hq (Ne.symm hq2)).1, (ou_other Nat.prime_two hq (Ne.symm hq2)).2,
      (ou_other Nat.prime_two hq' (Ne.symm hq2')).1,
      (ou_other Nat.prime_two hq' (Ne.symm hq2')).2,
      (ou_self hq).1, (ou_self hq).2, (ou_other hq hq' hqq).1, (ou_other hq hq' hqq).2,
      (ou_other hq' hq (Ne.symm hqq)).1, (ou_other hq' hq (Ne.symm hqq)).2,
      (ou_self hq').1, (ou_self hq').2]
    simp only [pow_zero, mul_one, pow_one, jacobiSym.one_left, one_mul, mul_zero]
    rw [ite_eq_right (by omega)]

    have hQR := jacobiSym.quadratic_reciprocity (hq.odd_of_ne_two hq2)
      (hq'.odd_of_ne_two hq2')

    have hJ : IsSign (J((q' : ℤ) | q)) := jacobiSym_isSign hq (not_natCast_dvd_prime hq hq' hqq)
    have hJJ : J((q' : ℤ) | q) * J((q : ℤ) | q') = (-1) ^ (q / 2 * (q' / 2)) := by
      rw [hQR]
      rcases hJ with h | h <;> simp [h]
    have hsgn : sgn4 q q' = (-1) ^ (q / 2 * (q' / 2)) := by
      unfold sgn4
      rw [Int.cast_natCast, Int.cast_natCast,
        χ₄_eq_neg_one_pow (Nat.odd_iff.mp (hq.odd_of_ne_two hq2)),
        χ₄_eq_neg_one_pow (Nat.odd_iff.mp (hq'.odd_of_ne_two hq2')), pow_mul]
      rcases Nat.even_or_odd (q' / 2) with he | ho
      · rw [he.neg_one_pow, ite_eq_right (by norm_num)]
        rcases neg_one_pow_eq_or ℤ (q / 2) with h | h <;> rw [h] <;> simp [he.neg_one_pow]
      · rw [ho.neg_one_pow, ite_eq_left rfl]
        rcases neg_one_pow_eq_or ℤ (q / 2) with h | h <;> rw [h] <;> simp [ho.neg_one_pow]
    rw [hJJ, hsgn, ← pow_add, ← two_mul, pow_mul]
    simp

private theorem int_prime_eq {p : ℤ} (hp : Prime p) :
    ∃ q : ℕ, q.Prime ∧ (p = q ∨ p = -1 * q) := by
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.mp hp, ?_⟩
  rcases Int.natAbs_eq p with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [neg_one_mul]; exact h)

private theorem pf_neg_one_all : ∀ b : ℤ, b ≠ 0 → PF (-1) b := by
  intro b
  refine UniqueFactorizationMonoid.induction_on_prime b (fun h ↦ absurd rfl h) ?_ ?_
  · intro x hx _
    rcases Int.isUnit_iff.mp hx with rfl | rfl
    · exact pf_symm one_ne_zero (by norm_num) (pf_one_left (-1))
    · exact pf_neg_one_neg_one
  · intro a p ha hp ih _
    have hp0 : p ≠ 0 := hp.ne_zero
    have hgen : PF (-1) p := by
      obtain ⟨q, hq, rfl | rfl⟩ := int_prime_eq hp
      · by_cases hq2 : q = 2
        · subst hq2; exact_mod_cast pf_neg_one_two
        · exact pf_neg_one_prime hq hq2
      · refine pf_mul_right (by norm_num) (by norm_num) (by exact_mod_cast hq.ne_zero)
          pf_neg_one_neg_one ?_
        by_cases hq2 : q = 2
        · subst hq2; exact_mod_cast pf_neg_one_two
        · exact pf_neg_one_prime hq hq2
    exact pf_mul_right (by norm_num) hp0 ha hgen (ih ha)

private theorem pf_natPrime_natPrime {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime) : PF q q' := by
  by_cases hqq : q = q'
  · subst hqq
    by_cases hq2 : q = 2
    · subst hq2; exact_mod_cast pf_two_two
    · exact pf_prime_self hq hq2
  by_cases hq2 : q = 2
  · subst hq2; exact_mod_cast pf_two_prime hq' (Ne.symm hqq)
  by_cases hq2' : q' = 2
  · subst hq2'
    exact pf_symm (by exact_mod_cast hq'.ne_zero) (by exact_mod_cast hq.ne_zero)
      (by exact_mod_cast pf_two_prime hq hq2)
  exact pf_prime_prime hq hq2 hq' hq2' hqq

private theorem pf_natPrime_all {q : ℕ} (hq : q.Prime) : ∀ b : ℤ, b ≠ 0 → PF q b := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  intro b
  refine UniqueFactorizationMonoid.induction_on_prime b (fun h ↦ absurd rfl h) ?_ ?_
  · intro x hx _
    rcases Int.isUnit_iff.mp hx with rfl | rfl
    · exact pf_symm one_ne_zero hq0 (pf_one_left q)
    · exact pf_symm (by norm_num) hq0 (pf_neg_one_all q hq0)
  · intro a p ha hp ih _
    have hgen : PF q p := by
      obtain ⟨q', hq', rfl | rfl⟩ := int_prime_eq hp
      · exact pf_natPrime_natPrime hq hq'
      · exact pf_mul_right hq0 (by norm_num) (by exact_mod_cast hq'.ne_zero)
          (pf_symm (by norm_num) hq0 (pf_neg_one_all q hq0)) (pf_natPrime_natPrime hq hq')
    exact pf_mul_right hq0 hp.ne_zero ha hgen (ih ha)

private theorem pf_intPrime_all {p : ℤ} (hp : Prime p) (b : ℤ) (hb : b ≠ 0) : PF p b := by
  obtain ⟨q, hq, rfl | rfl⟩ := int_prime_eq hp
  · exact pf_natPrime_all hq b hb
  · exact pf_mul_left (by norm_num) (by exact_mod_cast hq.ne_zero) (pf_neg_one_all b hb)
      (pf_natPrime_all hq b hb)

private theorem pf_all (a : ℤ) : a ≠ 0 → ∀ b : ℤ, b ≠ 0 → PF a b := by
  refine UniqueFactorizationMonoid.induction_on_prime a (fun h ↦ absurd rfl h) ?_ ?_
  · intro x hx _ b hb
    rcases Int.isUnit_iff.mp hx with rfl | rfl
    · exact pf_one_left b
    · exact pf_neg_one_all b hb
  · intro a p ha hp ih _ b hb
    exact pf_mul_left hp.ne_zero ha (pf_intPrime_all hp b hb) (ih ha b hb)

end HilbertRecipPort

namespace HilbertRecipPort

section Padic

open HilbertRecipOddPort

variable {p : ℕ} [hp : Fact p.Prime]

private theorem norm_intCast_eq_one_of_not_dvd {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) : ‖(u : ℚ_[p])‖ = 1 :=
  le_antisymm (Padic.norm_int_le_one u)
    (not_lt.mp fun h ↦ hu (Padic.norm_intCast_lt_one_iff.mp h))

private theorem natCast_p_ne_zero : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero

private theorem isSquare_intCast_iff_jacobiSym (hp2 : p ≠ 2) {v : ℤ} (hv : ¬ (p : ℤ) ∣ v) :
    IsSquare (v : ℚ_[p]) ↔ J(v | p) = 1 := by
  have hv0 : ((v : ZMod p)) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hv
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hv0]
  have hres : PadicInt.toZMod ((v : ℤ_[p])) = (v : ZMod p) := map_intCast _ v
  constructor
  · rintro ⟨w, hw⟩
    have hvn : ‖(v : ℚ_[p])‖ = 1 := norm_intCast_eq_one_of_not_dvd hv
    have hwn : ‖w‖ ≤ 1 := by
      have : ‖w‖ * ‖w‖ = 1 := by rw [← norm_mul, ← hw, hvn]
      nlinarith [norm_nonneg w]
    set W : ℤ_[p] := ⟨w, hwn⟩
    have hVW : (v : ℤ_[p]) = W * W := by
      apply Subtype.val_injective
      simp only [PadicInt.coe_mul, PadicInt.coe_intCast, W]
      exact hw
    refine ⟨PadicInt.toZMod W, ?_⟩
    rw [← hres, hVW, map_mul]
  · rintro ⟨s, hs⟩
    have hs0 : s ≠ 0 := by rintro rfl; exact hv0 (by simpa using hs)
    obtain ⟨t, ht⟩ := exists_sq_eq_of_toZMod_eq_sq hp2 (c := (v : ℤ_[p])) hs0
      (by rw [hres, hs, sq])
    refine ⟨t, ?_⟩
    have := congrArg ((↑) : ℤ_[p] → ℚ_[p]) ht
    simp only [PadicInt.coe_pow, PadicInt.coe_intCast] at this
    rw [← this, sq]

private theorem local_odd (hp2 : p ≠ 2) {u v : ℤ} (hu : ¬ (p : ℤ) ∣ u) (hv : ¬ (p : ℤ) ∣ v)
    {i j : ℕ} (hi : i = 0 ∨ i = 1) (hj : j = 0 ∨ j = 1) :
    Iso ((p : ℚ_[p]) ^ i * u) ((p : ℚ_[p]) ^ j * v) ↔
      χ₄ (p : ℤ) ^ (i * j) * J(u | p) ^ j * J(v | p) ^ i = 1 := by
  have hU : ‖(u : ℚ_[p])‖ = 1 := norm_intCast_eq_one_of_not_dvd hu
  have hV : ‖(v : ℚ_[p])‖ = 1 := norm_intCast_eq_one_of_not_dvd hv
  have hU0 : (u : ℚ_[p]) ≠ 0 := fun h ↦ by simp [h] at hU
  have hP := natCast_p_ne_zero (p := p)
  have hJu := jacobiSym_isSign hp.out hu
  have hJv := jacobiSym_isSign hp.out hv
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  ·
    simp only [pow_zero, one_mul, mul_zero, mul_one, iff_true]
    exact Padic.exists_ternary_isotropic_of_norm_eq_one_of_ne_two p hp2 _ _ hU hV
  ·
    simp only [pow_zero, one_mul, pow_one, mul_one]
    rw [iso_comm]
    change (∃ z x y : ℚ_[p], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - ((p : ℚ_[p]) * v) * x ^ 2 - u * y ^ 2 = 0) ↔ _
    rw [Padic.exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two p hp2 _ _ hV hU,
      isSquare_intCast_iff_jacobiSym hp2 hu]
  ·
    simp only [pow_zero, one_mul, pow_one, mul_zero, mul_one]
    change (∃ z x y : ℚ_[p], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - ((p : ℚ_[p]) * u) * x ^ 2 - v * y ^ 2 = 0) ↔ _
    rw [Padic.exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two p hp2 _ _ hU hV,
      isSquare_intCast_iff_jacobiSym hp2 hv]
  ·
    simp only [pow_one, mul_one]
    have hnuv : ¬ (p : ℤ) ∣ -(u * v) := by
      rw [dvd_neg]
      intro h
      rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_or_dvd h with h | h
      · exact hu h
      · exact hv h
    have hW : ‖((-(u * v) : ℤ) : ℚ_[p])‖ = 1 := norm_intCast_eq_one_of_not_dvd hnuv
    have step1 : Iso ((p : ℚ_[p]) * u) ((p : ℚ_[p]) * v) ↔
        Iso ((p : ℚ_[p]) * u) ((-(u * v) : ℤ) : ℚ_[p]) := by
      rw [← iso_mul_sq_right (A := (p : ℚ_[p]) * u) hU0,
        ← iso_neg_mul (B := ((-(u * v) : ℤ) : ℚ_[p])) (mul_ne_zero hP hU0)]
      push_cast
      ring_nf
    rw [step1]
    change (∃ z x y : ℚ_[p], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - ((p : ℚ_[p]) * u) * x ^ 2 - ((-(u * v) : ℤ) : ℚ_[p]) * y ^ 2 = 0) ↔ _
    rw [Padic.exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two p hp2 _ _ hU hW,
      isSquare_intCast_iff_jacobiSym hp2 hnuv, jacobiSym.neg _ hpodd, jacobiSym.mul_left]
    have e : χ₄ ((p : ℤ) : ZMod 4) = χ₄ (p : ZMod 4) := by rw [Int.cast_natCast]
    rw [e, mul_assoc]

end Padic

section Two

private theorem dvd8_iff (e : ℤ) : (2 : ℤ) ^ 3 ∣ e ↔ ((e : ZMod 8)) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num

private theorem dvd4_iff (e : ℤ) : (2 : ℤ) ^ 2 ∣ e ↔ (ZMod.cast (e : ZMod 8) : ZMod 4) = 0 := by
  rw [ZMod.cast_intCast (show 4 ∣ 8 by norm_num), ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num

private theorem sq_zmod8 {u : ℤ} (hu : ¬ (2 : ℤ) ∣ u) : (u : ZMod 8) * (u : ZMod 8) = 1 := by
  have h8 : (8 : ℤ) ∣ u * u - 1 := by
    have : u % 8 = 1 ∨ u % 8 = 3 ∨ u % 8 = 5 ∨ u % 8 = 7 := by omega
    rcases this with h | h | h | h <;>
    · have := Int.emod_emod_of_dvd u (show (8 : ℤ) ∣ 8 by norm_num)
      apply Int.dvd_of_emod_eq_zero
      simp [Int.sub_emod, Int.mul_emod, h]
  have : ((u * u - 1 : ℤ) : ZMod 8) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h8
  push_cast at this
  exact sub_eq_zero.mp this

private theorem sgn4_eq (u v : ℤ) : sgn4 u v =
    if χ₄ (ZMod.cast (v : ZMod 8) : ZMod 4) = -1 then χ₄ (ZMod.cast (u : ZMod 8) : ZMod 4)
    else 1 := by
  unfold sgn4
  rw [ZMod.cast_intCast (show 4 ∣ 8 by norm_num), ZMod.cast_intCast (show 4 ∣ 8 by norm_num)]

private theorem D00 : ∀ x y : ZMod 8, x * x = 1 → y * y = 1 →
    ((if χ₄ (ZMod.cast y : ZMod 4) = -1 then χ₄ (ZMod.cast x : ZMod 4) else 1) = 1 ↔
      ((ZMod.cast (x - 1) : ZMod 4) = 0 ∨ (ZMod.cast (y - 1) : ZMod 4) = 0)) := by decide

private theorem D10 : ∀ x y : ZMod 8, x * x = 1 → y * y = 1 →
    ((if χ₄ (ZMod.cast y : ZMod 4) = -1 then χ₄ (ZMod.cast x : ZMod 4) else 1) * χ₈ y = 1 ↔
      (y - 1 = 0 ∨ 2 * x + y - 1 = 0)) := by decide

private theorem D01 : ∀ x y : ZMod 8, x * x = 1 → y * y = 1 →
    ((if χ₄ (ZMod.cast y : ZMod 4) = -1 then χ₄ (ZMod.cast x : ZMod 4) else 1) * χ₈ x = 1 ↔
      (x - 1 = 0 ∨ 2 * y + x - 1 = 0)) := by decide

private theorem D11 : ∀ x y : ZMod 8, x * x = 1 → y * y = 1 →
    ((if χ₄ (ZMod.cast y : ZMod 4) = -1 then χ₄ (ZMod.cast x : ZMod 4) else 1) * χ₈ x * χ₈ y
        = 1 ↔ (-(x * y) - 1 = 0 ∨ 2 * x + -(x * y) - 1 = 0)) := by decide

private theorem L00 {u v : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hv : ¬ (2 : ℤ) ∣ v) :
    sgn4 u v = 1 ↔ (2 : ℤ) ^ 2 ∣ u - 1 ∨ (2 : ℤ) ^ 2 ∣ v - 1 := by
  rw [dvd4_iff, dvd4_iff, sgn4_eq]; push_cast
  exact D00 _ _ (sq_zmod8 hu) (sq_zmod8 hv)

private theorem L10 {u v : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hv : ¬ (2 : ℤ) ∣ v) :
    sgn4 u v * χ₈ v = 1 ↔ (2 : ℤ) ^ 3 ∣ v - 1 ∨ (2 : ℤ) ^ 3 ∣ 2 * u + v - 1 := by
  rw [dvd8_iff, dvd8_iff, sgn4_eq]; push_cast
  exact D10 _ _ (sq_zmod8 hu) (sq_zmod8 hv)

private theorem L01 {u v : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hv : ¬ (2 : ℤ) ∣ v) :
    sgn4 u v * χ₈ u = 1 ↔ (2 : ℤ) ^ 3 ∣ u - 1 ∨ (2 : ℤ) ^ 3 ∣ 2 * v + u - 1 := by
  rw [dvd8_iff, dvd8_iff, sgn4_eq]; push_cast
  exact D01 _ _ (sq_zmod8 hu) (sq_zmod8 hv)

private theorem L11 {u v : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hv : ¬ (2 : ℤ) ∣ v) :
    sgn4 u v * χ₈ u * χ₈ v = 1 ↔
      (2 : ℤ) ^ 3 ∣ -(u * v) - 1 ∨ (2 : ℤ) ^ 3 ∣ 2 * u + -(u * v) - 1 := by
  rw [dvd8_iff, dvd8_iff, sgn4_eq]; push_cast
  exact D11 _ _ (sq_zmod8 hu) (sq_zmod8 hv)

private theorem norm_intCast_le_two (k : ℤ) :
    ‖(k : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-2 : ℤ) ↔ (2 : ℤ) ^ 2 ∣ k := by
  have := Padic.norm_int_le_pow_iff_dvd (p := 2) k 2
  exact_mod_cast this

private theorem norm_intCast_le_three (k : ℤ) :
    ‖(k : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-3 : ℤ) ↔ (2 : ℤ) ^ 3 ∣ k := by
  have := Padic.norm_int_le_pow_iff_dvd (p := 2) k 3
  exact_mod_cast this

private theorem local_two {u v : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hv : ¬ (2 : ℤ) ∣ v)
    {i j : ℕ} (hi : i = 0 ∨ i = 1) (hj : j = 0 ∨ j = 1) :
    Iso ((2 : ℚ_[2]) ^ i * u) ((2 : ℚ_[2]) ^ j * v) ↔
      sgn4 u v * χ₈ u ^ j * χ₈ v ^ i = 1 := by
  have hu' : ¬ ((2 : ℕ) : ℤ) ∣ u := by exact_mod_cast hu
  have hv' : ¬ ((2 : ℕ) : ℤ) ∣ v := by exact_mod_cast hv
  have hU : ‖(u : ℚ_[2])‖ = 1 := norm_intCast_eq_one_of_not_dvd hu'
  have hV : ‖(v : ℚ_[2])‖ = 1 := norm_intCast_eq_one_of_not_dvd hv'
  have hU0 : (u : ℚ_[2]) ≠ 0 := fun h ↦ by simp [h] at hU
  have h20 : (2 : ℚ_[2]) ≠ 0 := by exact_mod_cast natCast_p_ne_zero (p := 2)
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  ·
    simp only [pow_zero, one_mul, mul_one]
    change (∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (u : ℚ_[2]) * x ^ 2 - v * y ^ 2 = 0) ↔ _
    rw [HilbertRecipDyadicUnitsPort.units_iff _ _ hU hV, L00 hu hv,
      show (u : ℚ_[2]) - 1 = ((u - 1 : ℤ) : ℚ_[2]) by push_cast; ring,
      show (v : ℚ_[2]) - 1 = ((v - 1 : ℤ) : ℚ_[2]) by push_cast; ring,
      norm_intCast_le_two, norm_intCast_le_two]
  ·
    simp only [pow_zero, one_mul, pow_one, mul_one]
    rw [iso_comm]
    change (∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (2 * (v : ℚ_[2])) * x ^ 2 - u * y ^ 2 = 0) ↔ _
    rw [HilbertRecipDyadicTwoMulPort.two_mul_iff _ _ hV hU, L01 hu hv,
      show (u : ℚ_[2]) - 1 = ((u - 1 : ℤ) : ℚ_[2]) by push_cast; ring,
      show 2 * (v : ℚ_[2]) + u - 1 = ((2 * v + u - 1 : ℤ) : ℚ_[2]) by push_cast; ring,
      norm_intCast_le_three, norm_intCast_le_three]
  ·
    simp only [pow_zero, pow_one, mul_one, one_mul]
    change (∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (2 * (u : ℚ_[2])) * x ^ 2 - v * y ^ 2 = 0) ↔ _
    rw [HilbertRecipDyadicTwoMulPort.two_mul_iff _ _ hU hV, L10 hu hv,
      show (v : ℚ_[2]) - 1 = ((v - 1 : ℤ) : ℚ_[2]) by push_cast; ring,
      show 2 * (u : ℚ_[2]) + v - 1 = ((2 * u + v - 1 : ℤ) : ℚ_[2]) by push_cast; ring,
      norm_intCast_le_three, norm_intCast_le_three]
  ·
    simp only [pow_one]
    have hnuv : ¬ ((2 : ℕ) : ℤ) ∣ -(u * v) := by
      rw [dvd_neg]
      intro h
      rcases (Nat.prime_iff_prime_int.mp Nat.prime_two).dvd_or_dvd h with h | h
      · exact hu' h
      · exact hv' h
    have hW : ‖((-(u * v) : ℤ) : ℚ_[2])‖ = 1 := norm_intCast_eq_one_of_not_dvd hnuv
    have step1 : Iso ((2 : ℚ_[2]) * u) ((2 : ℚ_[2]) * v) ↔
        Iso ((2 : ℚ_[2]) * u) ((-(u * v) : ℤ) : ℚ_[2]) := by
      rw [← iso_mul_sq_right (A := (2 : ℚ_[2]) * u) hU0,
        ← iso_neg_mul (B := ((-(u * v) : ℤ) : ℚ_[2])) (mul_ne_zero h20 hU0)]
      push_cast
      ring_nf
    rw [step1]
    change (∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (2 * (u : ℚ_[2])) * x ^ 2 - ((-(u * v) : ℤ) : ℚ_[2]) * y ^ 2 = 0) ↔ _
    rw [HilbertRecipDyadicTwoMulPort.two_mul_iff _ _ hU hW, L11 hu hv,
      show ((-(u * v) : ℤ) : ℚ_[2]) - 1 = ((-(u * v) - 1 : ℤ) : ℚ_[2]) by push_cast; ring,
      show 2 * (u : ℚ_[2]) + ((-(u * v) : ℤ) : ℚ_[2]) - 1 = ((2 * u + -(u * v) - 1 : ℤ) : ℚ_[2])
        by push_cast; ring,
      norm_intCast_le_three, norm_intCast_le_three]

end Two

private theorem iso_padic_iff_sym {p : ℕ} [hp : Fact p.Prime] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Iso (a : ℚ_[p]) (b : ℚ_[p]) ↔ sym p a b = 1 := by
  obtain ⟨hea, hua⟩ := decomp hp.out ha
  obtain ⟨heb, hub⟩ := decomp hp.out hb
  set α := ord p a
  set β := ord p b
  set u := unt p a
  set v := unt p b
  have hP := natCast_p_ne_zero (p := p)

  have hcast : ∀ (c w : ℤ) (γ : ℕ), c = (p : ℤ) ^ γ * w →
      (c : ℚ_[p]) = (p : ℚ_[p]) ^ (γ % 2) * w * ((p : ℚ_[p]) ^ (γ / 2)) ^ 2 := by
    intro c w γ h
    rw [h]; push_cast
    conv_lhs => rw [← Nat.div_add_mod γ 2]
    ring
  have hsq : ∀ γ : ℕ, ((p : ℚ_[p]) ^ (γ / 2)) ≠ 0 := fun γ ↦ pow_ne_zero _ hP
  have hIso : Iso (a : ℚ_[p]) (b : ℚ_[p]) ↔
      Iso ((p : ℚ_[p]) ^ (α % 2) * u) ((p : ℚ_[p]) ^ (β % 2) * v) := by
    rw [hcast a u α hea, hcast b v β heb,
      iso_mul_sq_left (hsq α), iso_comm, iso_mul_sq_left (hsq β), iso_comm]
  rw [hIso]
  have hi := Nat.mod_two_eq_zero_or_one α
  have hj := Nat.mod_two_eq_zero_or_one β
  by_cases hp2 : p = 2
  · subst hp2
    have hu2 : ¬ (2 : ℤ) ∣ u := by exact_mod_cast hua
    have hv2 : ¬ (2 : ℤ) ∣ v := by exact_mod_cast hub
    have := local_two hu2 hv2 hi hj
    push_cast at this ⊢
    rw [this]
    unfold sym symTwo
    rw [ite_eq_left rfl]
    change _ ↔ sgn4 u v * χ₈ u ^ β * χ₈ v ^ α = 1
    rw [(χ₈_isSign_of_odd hu2).pow_eq_pow_mod_two β, (χ₈_isSign_of_odd hv2).pow_eq_pow_mod_two α]
  · rw [local_odd hp2 hua hub hi hj]
    unfold sym symOdd
    rw [ite_eq_right hp2]
    change _ ↔ χ₄ (p : ℤ) ^ (α * β) * J(u | p) ^ β * J(v | p) ^ α = 1
    have h4 := χ₄_nat_isSign_of_ne_two hp.out hp2
    rw [(jacobiSym_isSign hp.out hua).pow_eq_pow_mod_two β,
      (jacobiSym_isSign hp.out hub).pow_eq_pow_mod_two α, h4.pow_eq_pow_mod_two (α * β),
      Nat.mul_mod, ← h4.pow_eq_pow_mod_two]

end HilbertRecipPort

namespace HilbertRecipPort

private theorem iso_map_of_injective {F L φ : Type*} [Field F] [Field L] [FunLike φ F L]
    [RingHomClass φ F L] (f : φ) (hf : Function.Injective f) {A B : F} (h : Iso A B) :
    Iso (f A) (f B) := by
  obtain ⟨z, x, y, hnt, heq⟩ := h
  refine ⟨f z, f x, f y, ?_, by simpa [map_sub, map_mul, map_pow] using congrArg f heq⟩
  rintro ⟨hz, hx, hy⟩
  exact hnt ⟨(map_eq_zero_iff f hf).mp hz, (map_eq_zero_iff f hf).mp hx,
    (map_eq_zero_iff f hf).mp hy⟩

private theorem cast_num_mul_den {p : ℕ} [Fact p.Prime] (c : ℚ) :
    ((c.num * c.den : ℤ) : ℚ_[p]) = (c : ℚ_[p]) * ((c.den : ℚ_[p])) ^ 2 := by
  have h : ((c.num : ℤ) : ℚ_[p]) = ((c * c.den : ℚ) : ℚ_[p]) := by
    rw [Rat.mul_den_eq_num, Rat.cast_intCast]
  calc ((c.num * c.den : ℤ) : ℚ_[p]) = ((c.num : ℤ) : ℚ_[p]) * (c.den : ℚ_[p]) := by push_cast; ring
    _ = ((c * c.den : ℚ) : ℚ_[p]) * (c.den : ℚ_[p]) := by rw [h]
    _ = _ := by push_cast; ring

private theorem iso_ratCast_padic_iff_sym {p : ℕ} [Fact p.Prime] {a b : ℚ} (ha : a ≠ 0) (hb : b ≠
  0) :
    Iso (a : ℚ_[p]) (b : ℚ_[p]) ↔ sym p (a.num * a.den) (b.num * b.den) = 1 := by
  have hA0 : a.num * a.den ≠ 0 :=
    mul_ne_zero (Rat.num_ne_zero.mpr ha) (by exact_mod_cast a.den_nz)
  have hB0 : b.num * b.den ≠ 0 :=
    mul_ne_zero (Rat.num_ne_zero.mpr hb) (by exact_mod_cast b.den_nz)
  have hda : ((a.den : ℚ_[p])) ≠ 0 := by exact_mod_cast a.den_nz
  have hdb : ((b.den : ℚ_[p])) ≠ 0 := by exact_mod_cast b.den_nz
  rw [← iso_padic_iff_sym hA0 hB0, cast_num_mul_den, cast_num_mul_den,
    iso_mul_sq_left hda, iso_mul_sq_right hdb]

private theorem sgnInf_num_mul_den (a b : ℚ) :
    sgnInf (a.num * a.den) (b.num * b.den) = if a < 0 ∧ b < 0 then -1 else 1 := by
  have key : ∀ c : ℚ, c.num * c.den < 0 ↔ c < 0 := by
    intro c
    have hden : (0 : ℤ) < c.den := by exact_mod_cast c.den_pos
    rw [← Rat.num_neg]
    constructor
    · intro h; nlinarith
    · intro h; exact mul_neg_of_neg_of_pos h hden
  unfold sgnInf
  simp only [key]

end HilbertRecipPort

open IsDedekindDomain NumberField HilbertRecipPort

private local instance instFactPrimesHR (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

private theorem iso_adicCompletion_iff (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℚ) :
    Iso (algebraMap ℚ (v.adicCompletion ℚ) a) (algebraMap ℚ (v.adicCompletion ℚ) b) ↔
      Iso (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])
        (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) := by
  set e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v with he
  have ha : (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) = algebraMap ℚ _ a :=
    (eq_ratCast _ a).symm
  have hb : (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) = algebraMap ℚ _ b :=
    (eq_ratCast _ b).symm
  rw [ha, hb]
  constructor
  · intro h
    have := iso_map_of_injective e e.injective h
    rwa [AlgEquivClass.commutes, AlgEquivClass.commutes] at this
  · intro h
    have := iso_map_of_injective e.symm e.symm.injective h
    rwa [AlgEquivClass.commutes, AlgEquivClass.commutes] at this

/-- **Hilbert reciprocity for ternary forms over `ℚ`.** For nonzero `a, b : ℚ`,
the finite places where `z ^ 2 - a * x ^ 2 - b * y ^ 2` is anisotropic are
finite in number, and their count plus `[a < 0 ∧ b < 0]` is even. -/
public theorem Rat.hilbertReciprocity_even_card_not_ternary_isotropic
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
      (∀ v, v ∈ S ↔
        ¬ ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
          z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2
            - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2 = 0) ∧
      Even (S.card + if (a < 0 ∧ b < 0) then 1 else 0) := by
  classical
  set A : ℤ := a.num * a.den with hA
  set B : ℤ := b.num * b.den with hB
  have hA0 : A ≠ 0 := mul_ne_zero (Rat.num_ne_zero.mpr ha) (by exact_mod_cast a.den_nz)
  have hB0 : B ≠ 0 := mul_ne_zero (Rat.num_ne_zero.mpr hb) (by exact_mod_cast b.den_nz)
  have hN0 : (2 * A * B).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]; exact mul_ne_zero (mul_ne_zero two_ne_zero hA0) hB0
  set π : HeightOneSpectrum (𝓞 ℚ) → ℕ :=
    fun v ↦ ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) with hπ_def
  have hπinj : Function.Injective π :=
    Subtype.val_injective.comp (Rat.HeightOneSpectrum.primesEquiv).injective
  set s : Finset ℕ := (2 * A * B).natAbs.primeFactors with hs_def
  set T : Finset ℕ := s.filter (fun p ↦ sym p A B = -1) with hT_def
  have hs : ∀ p ∈ s, p.Prime := fun p hp ↦ Nat.prime_of_mem_primeFactors hp
  have hsc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * A * B → p ∈ s := fun p hp hd ↦
    Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp hd, hN0⟩

  have hmemT : ∀ p : ℕ, p.Prime → (p ∈ T ↔ ¬ sym p A B = 1) := by
    intro p hp
    rw [hT_def, Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩; rw [h]; norm_num
    · intro h
      rcases sym_isSign hp hA0 hB0 with h1 | h1
      · exact absurd h1 h
      · refine ⟨?_, h1⟩
        by_contra hps
        exact h (sym_eq_one_of_not_dvd hp (fun hd ↦ hps (hsc p hp hd)))
  refine ⟨T.preimage π (Set.injOn_of_injective hπinj), fun v ↦ ?_, ?_⟩
  ·
    rw [Finset.mem_preimage, hmemT _ (Rat.HeightOneSpectrum.primesEquiv v).2]
    change ¬ _ ↔ ¬ Iso _ _
    rw [iso_adicCompletion_iff, iso_ratCast_padic_iff_sym ha hb]
  ·
    have hcard : (T.preimage π (Set.injOn_of_injective hπinj)).card = T.card := by
      rw [Finset.card_preimage]
      congr 1
      apply Finset.filter_true_of_mem
      intro p hp
      have hpT := (Finset.mem_filter.mp hp).1
      exact ⟨(Rat.HeightOneSpectrum.primesEquiv).symm ⟨p, hs p hpT⟩, by
        rw [hπ_def]
        exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)⟩
    have hprod : ∏ p ∈ s, sym p A B = sgnInf A B := pf_all A hA0 B hB0 s hs hsc
    rw [← Finset.prod_filter_mul_prod_filter_not s (fun p ↦ sym p A B = -1)] at hprod
    have h1 : ∏ p ∈ s with sym p A B = -1, sym p A B = (-1) ^ T.card := by
      rw [hT_def, Finset.prod_congr rfl (fun p hp ↦ (Finset.mem_filter.mp hp).2),
        Finset.prod_const]
    have h2 : ∏ p ∈ s with ¬ sym p A B = -1, sym p A B = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      obtain ⟨hps, hne⟩ := Finset.mem_filter.mp hp
      exact (sym_isSign (hs p hps) hA0 hB0).resolve_right hne
    rw [h1, h2, mul_one, hA, hB, sgnInf_num_mul_den] at hprod
    rw [hcard]
    split_ifs at hprod ⊢ with hneg
    · have hodd : ¬ Even T.card := fun he ↦ by
        rw [he.neg_one_pow] at hprod; norm_num at hprod
      rcases Nat.even_or_odd T.card with he | ho
      · exact absurd he hodd
      · exact ho.add_one
    · rw [add_zero]
      exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hprod
