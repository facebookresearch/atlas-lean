/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TruncatedLogDiscriminant
import all MathlibExt.NumberTheory.TruncatedLogDiscriminant
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Finiteness of square discriminants of truncated logarithmic polynomials

For fixed `m ≥ 1`, there are only finitely many primes `q` with `m * q ≡ 1
[MOD 4]` such that the discriminant of the truncated logarithmic polynomial
`F_{m * q}` is a square in `ℚ`.

Statements from Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39 (arXiv:2401.14138).
`F_n(x) = 1 + x + x²/2 + ⋯ + xⁿ/n` and the discriminant is Mathlib's
`Polynomial.discr`.

The reduction modulo `q` specializes the private lemmas of
`MathlibExt.NumberTheory.TruncatedLogDiscriminant` (the exponent-one case of its reduction modulo
a prime power), which this module imports with `import all`.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

namespace finite_primes_isSquare_discr_truncatedLog

open not_isSquare_discr_truncatedLog_three_five_seven_mul

private lemma reducedPoly_false (q m : ℕ) :
    reducedPoly q m false = ∑ i ∈ Finset.Icc 1 m, C ((i : ZMod q)⁻¹) * X ^ i := by
  simp [reducedPoly]

private lemma pow_pred_mul {R : Type*} [Monoid R] (a : R) {n : ℕ} (hn : 1 ≤ n) :
    a ^ n = a * a ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact pow_succ' a k

private lemma geom_factor {m q : ℕ} (hq : q.Prime) :
    (geomPoly (m * q) : (ZMod q)[X]) = (X - 1) ^ (q - 1) * (geomPoly m) ^ q := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hchar : ((X : (ZMod q)[X]) ^ m - 1) ^ q = ((X : (ZMod q)[X]) ^ m) ^ q - 1 := by
    rw [sub_pow_char, one_pow]
  have h1 : (X : (ZMod q)[X]) ^ (m * q) - 1 = ((X : (ZMod q)[X]) ^ m - 1) ^ q := by
    rw [hchar, ← pow_mul]
  have hgeom : ((X : (ZMod q)[X]) - 1) * geomPoly (m * q) =
      (X : (ZMod q)[X]) ^ (m * q) - 1 := by
    have h := geom_sum_mul (X : (ZMod q)[X]) (m * q)
    rw [mul_comm] at h
    exact h
  have hgeom_m : ((X : (ZMod q)[X]) - 1) * geomPoly m = (X : (ZMod q)[X]) ^ m - 1 := by
    have h := geom_sum_mul (X : (ZMod q)[X]) m
    rw [mul_comm] at h
    exact h
  have hX1 : ((X : (ZMod q)[X]) - 1) ≠ 0 := by
    simpa using X_sub_C_ne_zero (1 : ZMod q)
  have hqpow : ((X : (ZMod q)[X]) - 1) ^ q =
      ((X : (ZMod q)[X]) - 1) * ((X : (ZMod q)[X]) - 1) ^ (q - 1) :=
    pow_pred_mul ((X : (ZMod q)[X]) - 1) hq.one_le
  have hfactor : ((X : (ZMod q)[X]) - 1) * geomPoly (m * q) =
      ((X : (ZMod q)[X]) - 1) * ((X - 1) ^ (q - 1) * (geomPoly m) ^ q) := by
    rw [hgeom, h1, ← hgeom_m, mul_pow, hqpow, mul_assoc]
  exact mul_left_cancel₀ hX1 hfactor

private lemma resultant_geom_factor {m q : ℕ} (hq : q.Prime) (hm : 1 ≤ m) (g : (ZMod q)[X]) :
    resultant (geomPoly (m * q) : (ZMod q)[X]) (g) =
      (g).eval 1 ^ (q - 1) * resultant (geomPoly m) (g) ^ q := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hm0 : 0 < m := by omega
  have hXC : ((X : (ZMod q)[X]) - 1) = X - C (1 : ZMod q) := by simp
  have hX1 : ((X : (ZMod q)[X]) - 1) ≠ 0 := by
    simpa using X_sub_C_ne_zero (1 : ZMod q)
  have hmonic_m : (geomPoly m : (ZMod q)[X]).Monic :=
    monic_geom_sum_X (by omega : m ≠ 0)
  have hdeg1 : (((X : (ZMod q)[X]) - 1) ^ (q - 1)).natDegree = q - 1 := by
    rw [hXC, natDegree_pow, natDegree_X_sub_C, mul_one]
  have hdeg2 : (((geomPoly m : (ZMod q)[X])) ^ q).natDegree = q * (m - 1) := by
    rw [natDegree_pow, geomPoly_degree hm0]
  have hmul := resultant_mul_left ((X - 1 : (ZMod q)[X]) ^ (q - 1)) ((geomPoly m) ^ q)
    (g) ((g).natDegree) le_rfl
  rw [hdeg1, hdeg2] at hmul
  have h1 := resultant_X_sub_C_pow_left (1 : ZMod q) (g) (q - 1)
    ((g).natDegree) le_rfl
  rw [← hXC] at h1
  have h2 := resultant_pow_left (f := (geomPoly m : (ZMod q)[X])) (g := g)
    (m := q) (n := (g).natDegree)
    (by rw [hmonic_m.leadingCoeff, one_pow]; exact one_ne_zero) le_rfl
  rw [hdeg2] at h2
  have hdegmul : (((X - 1 : (ZMod q)[X]) ^ (q - 1)) * (geomPoly m) ^ q).natDegree =
      (q - 1) + q * (m - 1) := by
    rw [natDegree_mul (pow_ne_zero _ hX1) (pow_ne_zero _ hmonic_m.ne_zero), hdeg1, hdeg2]
  rw [geom_factor hq, hdegmul, hmul, h1, h2]

private noncomputable def excA (m : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc 1 m, ((Nat.factorial m / i : ℕ) : ℤ)

private noncomputable def excG (m : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.Icc 1 m, C ((Nat.factorial m / i : ℕ) : ℤ) * X ^ i

private noncomputable def excR (m : ℕ) : ℤ :=
  resultant (geomPoly m : ℤ[X]) (excG m)

private lemma excG_coeff (m j : ℕ) :
    (excG m).coeff j =
      if j = 0 then 0 else if j ≤ m then ((Nat.factorial m / j : ℕ) : ℤ) else 0 := by
  classical
  by_cases h0 : j = 0
  · subst j
    simp [excG, coeff_X_pow, mul_ite, Finset.mem_Icc]
  · have hj : 1 ≤ j := by omega
    simp [excG, coeff_X_pow, mul_ite, Finset.mem_Icc, h0, hj]

private lemma cast_div_factorial {m q : ℕ} (hq : q.Prime) (hlt : m < q)
    {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) :
    (((Nat.factorial m / i : ℕ) : ℤ) : ZMod q) =
      ((Nat.factorial m : ℕ) : ZMod q) * ((i : ZMod q)⁻¹) := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hiz : (i : ZMod q) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun h => (Nat.lt_of_le_of_lt him hlt).not_ge (Nat.le_of_dvd (by omega : 0 < i) h)
  have hdiv : i ∣ Nat.factorial m := Nat.dvd_factorial (by omega : 0 < i) him
  rw [Int.cast_natCast, ← div_eq_mul_inv, eq_div_iff hiz, ← Nat.cast_mul]
  congr 1
  exact Nat.div_mul_cancel hdiv

private lemma eval_one_eq (q m : ℕ) :
    (reducedPoly q m false).eval 1 = ∑ i ∈ Finset.Icc 1 m, ((i : ZMod q)⁻¹) := by
  rw [reducedPoly_false, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  simp [eval_mul, eval_pow, eval_C, eval_X]

private lemma dvd_excA_of_eval_eq_zero {m q : ℕ} (hq : q.Prime) (hlt : m < q)
    (h0 : (reducedPoly q m false).eval 1 = 0) : (q : ℤ) ∣ excA m := by
  have hcast : ((excA m : ℤ) : ZMod q) =
      ((Nat.factorial m : ℕ) : ZMod q) * (reducedPoly q m false).eval 1 := by
    rw [excA, Int.cast_sum, eval_one_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact cast_div_factorial hq hlt (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
  have h0' : ((excA m : ℤ) : ZMod q) = 0 := by rw [hcast, h0, mul_zero]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0'

private lemma excA_pos {m : ℕ} (hm : 1 ≤ m) : 0 < excA m := by
  rw [excA]
  apply Finset.sum_pos
  · intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have him : i ≤ m := (Finset.mem_Icc.mp hi).2
    have hpos : 0 < Nat.factorial m / i := Nat.div_pos
      (Nat.le_of_dvd (Nat.factorial_pos m) (Nat.dvd_factorial (by omega : 0 < i) him))
      (by omega : 0 < i)
    exact_mod_cast hpos
  · exact Finset.nonempty_Icc.mpr hm

private lemma excG_natDegree {m : ℕ} (hm : 1 ≤ m) : (excG m).natDegree = m := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [excG_coeff, ite_eq_right (by omega : j ≠ 0), ite_eq_right (by omega : ¬ j ≤ m)]
  · rw [excG_coeff, ite_eq_right (by omega : m ≠ 0), ite_eq_left le_rfl]
    have hpos : 0 < Nat.factorial m / m := Nat.div_pos
      (Nat.le_of_dvd (Nat.factorial_pos m) (Nat.dvd_factorial (by omega : 0 < m) le_rfl))
      (by omega : 0 < m)
    exact_mod_cast hpos.ne'

private lemma excG_map {m q : ℕ} (hq : q.Prime) (hlt : m < q) :
    (excG m).map (Int.castRingHom (ZMod q)) =
      C (((Nat.factorial m : ℕ)) : ZMod q) * reducedPoly q m false := by
  rw [excG, reducedPoly_false, Polynomial.map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, Int.coe_castRingHom,
    ← mul_assoc, ← C_mul]
  congr 1
  congr 1
  exact cast_div_factorial hq hlt (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2

private lemma dvd_excR_of_resultant_eq_zero {m q : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hlt : m < q)
    (h0 : resultant (geomPoly m : (ZMod q)[X]) (reducedPoly q m false) = 0) : (q : ℤ) ∣ excR m := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hm0 : 0 < m := by omega
  have hR : ((excR m : ℤ) : ZMod q) =
      (((Nat.factorial m : ℕ)) : ZMod q) ^ (m - 1) *
        resultant (geomPoly m : (ZMod q)[X]) (reducedPoly q m false) (m - 1)
          (excG m).natDegree := by
    rw [excR]
    change Int.castRingHom (ZMod q) (resultant (geomPoly m : ℤ[X]) (excG m)) = _
    rw [geomPoly_degree hm0, ← resultant_map_map, geomPoly_map, excG_map hq hlt,
      resultant_C_mul_right]
  have hdegeq : resultant (geomPoly m : (ZMod q)[X]) (reducedPoly q m false) (m - 1)
      (excG m).natDegree =
      resultant (geomPoly m : (ZMod q)[X]) (reducedPoly q m false) := by
    have e1 : m - 1 = (geomPoly m : (ZMod q)[X]).natDegree := (geomPoly_degree hm0).symm
    have e2 : (excG m).natDegree = (reducedPoly q m false).natDegree := by
      rw [excG_natDegree hm, reducedPoly_degree (by omega) hlt false]
    rw [e1, e2]
  rw [hdegeq, h0, mul_zero] at hR
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hR

private noncomputable def auxPolyC (m : ℕ) : ℂ[X] :=
  C ((m : ℂ)⁻¹) + ∑ j ∈ Finset.Icc 1 (m - 1), C ((j : ℂ)⁻¹) * X ^ j

private noncomputable def remPolyC (m : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.Icc 2 (m - 1), C ((((j * (j - 1) : ℕ)) : ℂ)⁻¹) * X ^ j

private noncomputable def redPolyC (m : ℕ) : ℂ[X] :=
  ∑ i ∈ Finset.Icc 1 m, C ((i : ℂ)⁻¹) * X ^ i

private lemma auxPolyC_coeff (m j : ℕ) :
    (auxPolyC m).coeff j =
      if j = 0 then ((m : ℂ)⁻¹) else if j ≤ m - 1 then ((j : ℂ)⁻¹) else 0 := by
  classical
  by_cases h0 : j = 0
  · subst j
    simp [auxPolyC, coeff_X_pow, mul_ite, Finset.mem_Icc]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp [auxPolyC, coeff_X_pow, mul_ite, Finset.mem_Icc]

private lemma remPolyC_coeff (m j : ℕ) :
    (remPolyC m).coeff j =
      if 2 ≤ j ∧ j ≤ m - 1 then ((((j * (j - 1) : ℕ)) : ℂ)⁻¹) else 0 := by
  classical
  simp only [remPolyC, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_Icc]

private lemma redPolyC_coeff (m j : ℕ) :
    (redPolyC m).coeff j =
      if j = 0 then 0 else if j ≤ m then ((j : ℂ)⁻¹) else 0 := by
  classical
  by_cases h0 : j = 0
  · subst j
    simp [redPolyC, coeff_X_pow, mul_ite, Finset.mem_Icc]
  · have hj : 1 ≤ j := by omega
    simp [redPolyC, coeff_X_pow, mul_ite, Finset.mem_Icc, h0, hj]

private lemma aux_key_identity {m : ℕ} (hm : 2 ≤ m) :
    (1 - X) * auxPolyC m = (1 - X) * C ((m : ℂ)⁻¹) + X - C ((((m - 1 : ℕ)) : ℂ)⁻¹)
      - remPolyC m + C ((((m - 1 : ℕ)) : ℂ)⁻¹) * (1 - X ^ m) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm1C : (((m - 1 : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast (by omega : m - 1 ≠ 0)
  ext j
  simp only [sub_mul, one_mul, coeff_sub, coeff_add, auxPolyC_coeff, remPolyC_coeff,
    coeff_X, coeff_one, coeff_X_pow, coeff_C, coeff_C_mul]
  cases j with
  | zero =>
    simp only [coeff_X_mul_zero, ↓reduceIte, sub_zero]
    split_ifs
    all_goals (first | (exfalso; omega) | (field_simp; ring))
  | succ k =>
    have hk10 : k + 1 ≠ 0 := by omega
    by_cases hk0 : k = 0
    · subst k
      simp only [coeff_X_mul, coeff_C, auxPolyC_coeff, hk10, ↓reduceIte]
      split_ifs
      all_goals (first | (exfalso; omega) | (field_simp; ring))
    · have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
      have hk1C : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hk10
      have hkkC : ((((k + 1) * k : ℕ)) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.mul_ne_zero (by omega) hk0
      have e : k + 1 - 1 = k := by omega
      simp only [coeff_X_mul, coeff_C, auxPolyC_coeff, hk10, hk0, e, ↓reduceIte]
      split_ifs
      all_goals field_simp
      all_goals try push_cast
      all_goals (first | (exfalso; omega) | (rw [(by omega : m - 1 = k)]; ring) | ring)

private lemma sum_inv_mul_pred {m : ℕ} (hm : 2 ≤ m) :
    ∑ j ∈ Finset.Icc 2 (m - 1), ((((j * (j - 1) : ℕ)) : ℝ)⁻¹)
      = 1 - ((((m - 1 : ℕ)) : ℝ)⁻¹) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have h21 : (2:ℕ) - 1 = 1 := by decide
    rw [h21]
    have hempty : Finset.Icc 2 (1:ℕ) = ∅ := by decide
    rw [hempty, Finset.sum_empty]
    norm_num
  | succ n hn ih =>
    have e2 : n + 1 - 1 = n := Nat.add_sub_cancel n 1
    rw [e2]
    have e : n = (n - 1) + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ n)).symm
    conv_lhs => rw [e]
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ (n - 1) + 1), ih, ← e]
    have hnC : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hn1C : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : n - 1 ≠ 0)
    have hnnC : (((n * (n - 1) : ℕ)) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.mul_ne_zero (by omega) (by omega)
    have hsub : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    field_simp
    push_cast
    rw [hsub]
    ring

private lemma aux_ne_zero_of_pow {m : ℕ} (hm : 2 ≤ m) {θ : ℂ}
    (hpow : θ ^ m = 1) (hne : θ ≠ 1) : (auxPolyC m).eval θ ≠ 0 := by
  intro h0
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm1C : (((m - 1 : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast (by omega : m - 1 ≠ 0)
  have hmR : (0:ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm1R : (0:ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m - 1)
  have hnorm1 : ‖θ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow (by omega : m ≠ 0)
  set c : ℝ := ((m - 1 : ℕ) : ℝ) * (m : ℝ)⁻¹ with hc_def
  set d : ℝ := (m : ℝ)⁻¹ * (((m - 1 : ℕ) : ℝ)⁻¹) with hd_def
  have hc0 : 0 < c := by
    rw [hc_def]
    exact mul_pos hm1R (inv_pos.mpr hmR)
  have hd0 : 0 < d := by
    rw [hd_def]
    exact mul_pos (inv_pos.mpr hmR) (inv_pos.mpr hm1R)
  have hident := congrArg (Polynomial.eval θ) (aux_key_identity hm)
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one] at hident
  rw [h0, mul_zero, hpow, sub_self, mul_zero] at hident
  have hrem : (remPolyC m).eval θ =
      (1 - θ) * ((m : ℂ)⁻¹) + θ - ((((m - 1 : ℕ)) : ℂ)⁻¹) := by
    linear_combination hident
  have hrem2 : (remPolyC m).eval θ = ((c : ℝ) : ℂ) * θ - (((d : ℝ)) : ℂ) := by
    rw [hrem, hc_def, hd_def]
    push_cast
    have hsubC : ((((m - 1 : ℕ))) : ℂ) = (m : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    field_simp
    rw [hsubC]
    ring
  have hcd_eq : c - d = 1 - ((((m - 1 : ℕ)) : ℝ)⁻¹) := by
    rw [hc_def, hd_def]
    have e1 : (m : ℝ) ≠ 0 := hmR.ne'
    have e2 : (((m - 1 : ℕ)) : ℝ) ≠ 0 := hm1R.ne'
    have hsubR : (((m - 1 : ℕ)) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    field_simp
    rw [hsubR]
    ring
  have hle : ‖(remPolyC m).eval θ‖ ≤ 1 - ((((m - 1 : ℕ)) : ℝ)⁻¹) := by
    have heval : (remPolyC m).eval θ =
        ∑ j ∈ Finset.Icc 2 (m - 1), ((((j * (j - 1) : ℕ)) : ℂ)⁻¹) * θ ^ j := by
      rw [remPolyC, eval_finsetSum]
      apply Finset.sum_congr rfl
      intro j _
      rw [eval_mul, eval_C, eval_pow, eval_X]
    rw [heval]
    calc ‖∑ j ∈ Finset.Icc 2 (m - 1), ((((j * (j - 1) : ℕ)) : ℂ)⁻¹) * θ ^ j‖
        ≤ ∑ j ∈ Finset.Icc 2 (m - 1), ‖((((j * (j - 1) : ℕ)) : ℂ)⁻¹) * θ ^ j‖ :=
          norm_sum_le _ _
      _ = ∑ j ∈ Finset.Icc 2 (m - 1), ((((j * (j - 1) : ℕ)) : ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_mul, norm_inv, Complex.norm_natCast, norm_pow, hnorm1, one_pow, mul_one]
      _ = 1 - ((((m - 1 : ℕ)) : ℝ)⁻¹) := sum_inv_mul_pred hm
  have hge : c - d ≤ ‖((c : ℝ) : ℂ) * θ - ((d : ℝ) : ℂ)‖ := by
    have h := norm_sub_norm_le (((c:ℝ):ℂ) * θ) (((d:ℝ):ℂ))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, hnorm1, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0] at h
    exact h
  have heq : ‖((c : ℝ) : ℂ) * θ - ((d : ℝ) : ℂ)‖ = c - d := by
    have h2 : ‖(remPolyC m).eval θ‖ = ‖((c : ℝ) : ℂ) * θ - ((d : ℝ) : ℂ)‖ := by rw [hrem2]
    linarith [hle, hge, hcd_eq, h2]
  have hsq : ‖((c : ℝ) : ℂ) * θ - ((d : ℝ) : ℂ)‖ ^ 2 = (c - d) ^ 2 := by rw [heq]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hsq
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, Complex.mul_im, zero_mul, sub_zero, add_zero] at hsq
  have hnormθ2 : θ.re * θ.re + θ.im * θ.im = 1 := by
    have h := congrArg (· ^ 2) hnorm1
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h
    simpa using h
  have hexpand : (c * θ.re - d) * (c * θ.re - d) + (c * θ.im) * (c * θ.im) - (c - d) ^ 2
      = 2 * c * d * (1 - θ.re) + c ^ 2 * ((θ.re * θ.re + θ.im * θ.im) - 1) := by ring
  have h0' : (c * θ.re - d) * (c * θ.re - d) + (c * θ.im) * (c * θ.im) - (c - d) ^ 2 = 0 := by
    rw [hsq]; ring
  rw [h0', hnormθ2] at hexpand
  simp only [sub_self, mul_zero, add_zero] at hexpand
  have hcd0 : 2 * c * d ≠ 0 := by positivity
  have hre1 : θ.re = 1 := by
    have h10 : 1 - θ.re = 0 := (mul_eq_zero.mp hexpand.symm).resolve_left hcd0
    linarith
  have him0 : θ.im = 0 := by
    have hI : θ.im * θ.im = 0 := by
      have h := hnormθ2
      rw [hre1] at h
      linarith
    rcases mul_eq_zero.mp hI with h | h <;> exact h
  have hθ1 : θ = 1 := by
    apply Complex.ext
    · simpa using hre1
    · simpa using him0
  exact hne hθ1

private lemma redPolyC_ne_zero_of_pow {m : ℕ} (hm : 2 ≤ m) {θ : ℂ}
    (hpow : θ ^ m = 1) (hne : θ ≠ 1) : (redPolyC m).eval θ ≠ 0 := by
  have hred : (redPolyC m).eval θ = (auxPolyC m).eval θ := by
    have e1 : (redPolyC m).eval θ = ∑ i ∈ Finset.Icc 1 m, (((i : ℂ)⁻¹) * θ ^ i) := by
      rw [redPolyC, eval_finsetSum]
      apply Finset.sum_congr rfl
      intro i _
      rw [eval_mul, eval_C, eval_pow, eval_X]
    have e2 : (auxPolyC m).eval θ
        = ((m : ℂ)⁻¹) + ∑ j ∈ Finset.Icc 1 (m - 1), (((j : ℂ)⁻¹) * θ ^ j) := by
      rw [auxPolyC, eval_add, eval_C, eval_finsetSum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [eval_mul, eval_C, eval_pow, eval_X]
    rw [e1, e2]
    have hpeel : ∑ i ∈ Finset.Icc 1 m, (((i : ℂ)⁻¹) * θ ^ i)
        = ∑ i ∈ Finset.Icc 1 (m - 1), (((i : ℂ)⁻¹) * θ ^ i)
          + (((m : ℂ)⁻¹) * θ ^ m) := by
      have e : m = (m - 1) + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ m)).symm
      conv_lhs => rw [e]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ (m - 1) + 1), ← e]
    rw [hpeel, hpow, mul_one]
    exact add_comm _ _
  rw [hred]
  exact aux_ne_zero_of_pow hm hpow hne

private lemma redPolyC_natDegree {m : ℕ} (hm : 1 ≤ m) : (redPolyC m).natDegree = m := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [redPolyC_coeff, ite_eq_right (by omega : j ≠ 0), ite_eq_right (by omega : ¬ j ≤ m)]
  · rw [redPolyC_coeff, ite_eq_right (by omega : m ≠ 0), ite_eq_left le_rfl]
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    exact inv_ne_zero hmC

private lemma cast_div_factorial_C {m : ℕ}
    {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) :
    ((((Nat.factorial m / i : ℕ) : ℤ)) : ℂ) =
      (((Nat.factorial m : ℕ)) : ℂ) * (((i : ℂ)⁻¹)) := by
  have hiC : (i : ℂ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  have hdiv : i ∣ Nat.factorial m := Nat.dvd_factorial (by omega : 0 < i) him
  rw [Int.cast_natCast, ← div_eq_mul_inv, eq_div_iff hiC, ← Nat.cast_mul]
  congr 1
  exact Nat.div_mul_cancel hdiv

private lemma excG_map_C {m : ℕ} :
    (excG m).map (Int.castRingHom ℂ) =
      C (((Nat.factorial m : ℕ)) : ℂ) * redPolyC m := by
  rw [excG, redPolyC, Polynomial.map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, Int.coe_castRingHom,
    ← mul_assoc, ← C_mul]
  congr 1
  congr 1
  exact cast_div_factorial_C (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2

private lemma excR_eq {m : ℕ} (hm : 1 ≤ m) :
    ((excR m : ℤ) : ℂ) = (((Nat.factorial m : ℕ)) : ℂ) ^ (m - 1) *
      resultant (geomPoly m : ℂ[X]) (redPolyC m) (m - 1) m := by
  have hm0 : 0 < m := by omega
  rw [excR]
  change Int.castRingHom ℂ (resultant (geomPoly m : ℤ[X]) (excG m)) = _
  rw [geomPoly_degree hm0, ← resultant_map_map, geomPoly_map, excG_map_C,
    resultant_C_mul_right, excG_natDegree hm]

private lemma excR_ne_zero {m : ℕ} (hm : 1 ≤ m) : excR m ≠ 0 := by
  have hm0 : 0 < m := by omega
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hmonic : (geomPoly m : ℂ[X]).Monic := monic_geom_sum_X hm0.ne'
  have hfactor : ∀ θ ∈ (geomPoly m : ℂ[X]).roots, (redPolyC m).eval θ ≠ 0 := by
    intro θ hθ
    have h0 : (geomPoly m : ℂ[X]).eval θ = 0 := (mem_roots hmonic.ne_zero).mp hθ
    have hpow : θ ^ m = 1 := by
      have hsum := geom_sum_mul θ m
      have heval : (geomPoly m : ℂ[X]).eval θ = ∑ i ∈ Finset.range m, θ ^ i := by
        change (∑ i ∈ Finset.range m, (X : ℂ[X]) ^ i).eval θ = _
        rw [eval_finsetSum]
        apply Finset.sum_congr rfl
        intro i _
        rw [eval_pow, eval_X]
      rw [heval] at h0
      rw [h0, zero_mul] at hsum
      exact sub_eq_zero.mp hsum.symm
    have hne : θ ≠ 1 := by
      intro h1
      have heval1 : (geomPoly m : ℂ[X]).eval 1 = (m : ℂ) := by
        change (∑ i ∈ Finset.range m, (X : ℂ[X]) ^ i).eval 1 = _
        simp [eval_finsetSum]
      rw [h1, heval1] at h0
      exact hmC h0
    by_cases hm2 : 2 ≤ m
    · exact redPolyC_ne_zero_of_pow hm2 hpow hne
    · have hm1 : m = 1 := by omega
      rw [hm1, pow_one] at hpow
      exact absurd hpow hne
  have hprod := resultant_eq_prod_eval (geomPoly m : ℂ[X]) (redPolyC m) m
    (by rw [redPolyC_natDegree hm]) (IsAlgClosed.splits _)
  rw [geomPoly_degree hm0, hmonic.leadingCoeff, one_pow, one_mul] at hprod
  have hprod_ne : (Multiset.map (fun x => (redPolyC m).eval x)
      (geomPoly m : ℂ[X]).roots).prod ≠ 0 := by
    rw [ne_eq, Multiset.prod_eq_zero_iff]
    intro hmem
    obtain ⟨θ, hθ, heq⟩ := Multiset.mem_map.mp hmem
    exact hfactor θ hθ heq
  have hfact_ne : (((Nat.factorial m : ℕ)) : ℂ) ^ (m - 1) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Nat.factorial_pos m).ne')
  have hne0 : ((excR m : ℤ) : ℂ) ≠ 0 := by
    rw [excR_eq hm, hprod]
    exact mul_ne_zero hfact_ne hprod_ne
  intro hcon
  rw [hcon] at hne0
  simp at hne0

private lemma key_nonsquare {m q : ℕ} (hq : q.Prime) (hm : 1 ≤ m) (hlt : m < q)
    (h4 : m * q % 4 = 1) (hA : ¬ (q : ℤ) ∣ excA m) (hR : ¬ (q : ℤ) ∣ excR m) :
    ¬ IsSquare (truncatedLogPolynomial (m * q)).discr := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hlo : q ^ 1 ≤ m * q := by
    rw [pow_one]
    exact Nat.le_mul_of_pos_left q (by omega)
  have hhi : m * q < q ^ (1 + 1) := by
    rw [pow_two]
    exact Nat.mul_lt_mul_of_pos_right hlt hq.pos
  have hmz : (m : ZMod q) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun h => hlt.not_ge (Nat.le_of_dvd (by omega) h)
  refine nonsquare_of_odd_mul (Nat.odd_iff.mpr (by omega)) hmz fun hP0 => ?_
  have hu := lcm_quotient_ne_zero hlo hhi
  have hg : reducedPoly q (m * q / q ^ 1) (1 == 0) = reducedPoly q m false := by
    rw [pow_one, Nat.mul_div_cancel _ hq.pos]
    rfl
  rw [mod_resultant hlo hhi, hg, pow_one] at hP0
  rw [pow_one] at hu
  have hres0 : resultant (geomPoly (m * q) : (ZMod q)[X]) (reducedPoly q m false) ^ q = 0 :=
    (mul_eq_zero.mp hP0).resolve_left (pow_ne_zero _ hu)
  have hres0' : resultant (geomPoly (m * q) : (ZMod q)[X]) (reducedPoly q m false) = 0 := by
    by_contra hne
    exact pow_ne_zero q hne hres0
  rw [resultant_geom_factor hq hm] at hres0'
  rcases mul_eq_zero.mp hres0' with h | h
  · have heval0 : (reducedPoly q m false).eval 1 = 0 := by
      by_contra hne
      exact pow_ne_zero (q - 1) hne h
    exact hA (dvd_excA_of_eval_eq_zero hq hlt heval0)
  · have hresm0 : resultant (geomPoly m : (ZMod q)[X]) (reducedPoly q m false) = 0 := by
      by_contra hne
      exact pow_ne_zero q hne h
    exact hR (dvd_excR_of_resultant_eq_zero hq hm hlt hresm0)

end finite_primes_isSquare_discr_truncatedLog

/-- **Finiteness of square discriminants of $F_{mq}$ with $mq \equiv 1 \pmod 4$.** Let
$F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the truncated logarithmic polynomial and let
$m \ge 1$ be a natural number. Then there are only finitely many primes $q$ with
$mq \equiv 1 \pmod 4$ such that the discriminant of $F_{mq}$ is a square in $\mathbb{Q}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 3
(`integers-2025-A39-thm-3`). -/
public theorem finite_primes_isSquare_discr_truncatedLog {m : ℕ} (hm : 1 ≤ m) :
    {q : ℕ | q.Prime ∧ m * q % 4 = 1 ∧ IsSquare (truncatedLogPolynomial (m * q)).discr}.Finite := by
  have hfin : (Set.Iic m ∪ (Set.Iic
      (finite_primes_isSquare_discr_truncatedLog.excA m).natAbs ∪ Set.Iic
      (finite_primes_isSquare_discr_truncatedLog.excR m).natAbs)).Finite :=
    (Set.finite_Iic m).union ((Set.finite_Iic _).union (Set.finite_Iic _))
  apply hfin.subset
  intro q hq
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic] at hq ⊢
  obtain ⟨hqp, h4, hsq⟩ := hq
  by_cases hle : q ≤ m
  · tauto
  · have hlt : m < q := by omega
    by_cases hdvdA : (q : ℤ) ∣ finite_primes_isSquare_discr_truncatedLog.excA m
    · have hApos : 0 < (finite_primes_isSquare_discr_truncatedLog.excA m).natAbs :=
        Int.natAbs_pos.mpr
          (ne_of_gt (finite_primes_isSquare_discr_truncatedLog.excA_pos hm))
      have h1 : q ∣ (finite_primes_isSquare_discr_truncatedLog.excA m).natAbs := by
        have h2 : (Int.natAbs (q : ℤ)) ∣
            (finite_primes_isSquare_discr_truncatedLog.excA m).natAbs :=
          Int.natAbs_dvd_natAbs.mpr hdvdA
        rwa [Int.natAbs_natCast] at h2
      have hleA : q ≤ (finite_primes_isSquare_discr_truncatedLog.excA m).natAbs :=
        Nat.le_of_dvd hApos h1
      tauto
    · by_cases hdvdR : (q : ℤ) ∣ finite_primes_isSquare_discr_truncatedLog.excR m
      · have hRpos : 0 < (finite_primes_isSquare_discr_truncatedLog.excR m).natAbs :=
          Int.natAbs_pos.mpr
            (finite_primes_isSquare_discr_truncatedLog.excR_ne_zero hm)
        have h1 : q ∣ (finite_primes_isSquare_discr_truncatedLog.excR m).natAbs := by
          have h2 : (Int.natAbs (q : ℤ)) ∣
              (finite_primes_isSquare_discr_truncatedLog.excR m).natAbs :=
            Int.natAbs_dvd_natAbs.mpr hdvdR
          rwa [Int.natAbs_natCast] at h2
        have hleR : q ≤ (finite_primes_isSquare_discr_truncatedLog.excR m).natAbs :=
          Nat.le_of_dvd hRpos h1
        tauto
      · exfalso
        exact finite_primes_isSquare_discr_truncatedLog.key_nonsquare hqp hm hlt h4 hdvdA
          hdvdR hsq

end

end MetaMathlibExt
