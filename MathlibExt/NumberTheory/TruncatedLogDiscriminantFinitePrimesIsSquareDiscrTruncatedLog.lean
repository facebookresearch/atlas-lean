/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TruncatedLogDiscriminant
import all MathlibExt.NumberTheory.TruncatedLogDiscriminant
import MathlibExt.Analysis.Complex.EnestromKakeya
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

private noncomputable def redPolyC (m : ℕ) : ℂ[X] :=
  ∑ i ∈ Finset.Icc 1 m, C ((i : ℂ)⁻¹) * X ^ i

private lemma redPolyC_coeff (m j : ℕ) :
    (redPolyC m).coeff j =
      if j = 0 then 0 else if j ≤ m then ((j : ℂ)⁻¹) else 0 := by
  classical
  by_cases h0 : j = 0
  · subst j
    simp [redPolyC, coeff_X_pow, mul_ite, Finset.mem_Icc]
  · have hj : 1 ≤ j := by omega
    simp [redPolyC, coeff_X_pow, mul_ite, Finset.mem_Icc, h0, hj]

private lemma redPolyC_ne_zero_of_pow {m : ℕ} (hm : 2 ≤ m) {θ : ℂ} (hpow : θ ^ m = 1) :
    (redPolyC m).eval θ ≠ 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hnorm : ‖θ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow (by omega)
  have hθ : θ ≠ 0 := by
    rintro rfl
    simp at hnorm
  -- `redPolyC (n + 1) = X * Q`, where `Q` has the coefficients `1 / (k + 1)` for `k ≤ n`.
  let a : Fin (n + 1) → ℝ := fun k => ((k : ℕ) + 1 : ℝ)⁻¹
  have hpos : ∀ k, 0 < a k := fun k => by positivity
  have heval : (redPolyC (n + 1)).eval θ =
      θ * (∑ k : Fin (n + 1), C ((a k : ℝ) : ℂ) * X ^ (k : ℕ)).eval θ := by
    rw [redPolyC, eval_finsetSum, eval_finsetSum, sum_Icc_eq_range, Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [a, eval_mul, eval_C, eval_pow, eval_X]
    push_cast
    ring
  rw [heval]
  refine mul_ne_zero hθ fun hQ => ?_
  -- Every adjacent ratio `(k + 2) / (k + 1)` exceeds one, so every zero of `Q` has norm
  -- greater than one by the Eneström–Kakeya theorem.
  have hlow := (MathlibExt.Analysis.Complex.EnestromKakeya.enestrom_kakeya_zero_localization
    hn a hpos θ hQ).1
  rw [hnorm] at hlow
  have hgt : ∀ y ∈ Finset.image (fun k : Fin n => a k.castSucc / a k.succ) Finset.univ,
      1 < y := by
    intro y hy
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
    rw [one_lt_div (hpos _)]
    simp only [a, Fin.val_castSucc, Fin.val_succ]
    rw [inv_lt_inv₀ (by positivity) (by positivity)]
    push_cast
    linarith
  exact lt_irrefl _ (lt_of_lt_of_le ((Finset.lt_min'_iff _ _).mpr hgt) hlow)

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
    · exact redPolyC_ne_zero_of_pow hm2 hpow
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
