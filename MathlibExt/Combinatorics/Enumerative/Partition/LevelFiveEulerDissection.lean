/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import all MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
import all MathlibExt.Combinatorics.Enumerative.Partition.ReciprocalEulerDissection
import all MathlibExt.Combinatorics.Enumerative.Partition.OddDistinctsPentagonalRecurrence
import all MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProduct
import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# Two-dissection of the reciprocal Euler product at levels one and five

The theorem `one_div_f1_cube_f5_two_dissection` separates the even and odd powers in
`1 / (f₁³ f₅)`, with denominators cleared. Theta addition at moduli five and ten gives a
relation for the fourth power of `f₅ / f₁` and a two-term expansion for that quotient.
Inverting the argument of Dedekind eta gives the second relation needed to simplify the odd part.
-/

open PowerSeries

namespace MetaMathlibExt
namespace one_div_f1_cube_f5_two_dissection

open oddDistincts_pentagonal_recurrence (norm_pow_lt euler_ne multipliable_one_add_pow_lin
  odd_minus_prod odd_plus_prod)
open Analysis.SpecialFunctions.JacobiTripleProduct

private noncomputable abbrev E (q : ℂ) (k : ℕ) := eulerFunction (q ^ k)

private lemma E_ne {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) (hk : k ≠ 0 := by decide) :
    E q k ≠ 0 := euler_ne (norm_pow_lt hq hk)

private noncomputable def factors (s q : ℂ) (d r : ℕ) : ℂ :=
  ∏' n : ℕ, (1 + s * q ^ (d * n + r))

private lemma factors_prod {s q : ℂ} (hs : ‖s‖ ≤ 1) (hq : ‖q‖ < 1)
    (d r : ℕ) (hd : d ≠ 0 := by decide) :
    HasProd (fun n : ℕ ↦ 1 + s * q ^ (d * n + r)) (factors s q d r) :=
  (multipliable_one_add_pow_lin hq s hs d r hd).hasProd

/-- Split one progression into five progressions by the index modulo five. -/
private lemma factors_split {s q : ℂ} (hs : ‖s‖ ≤ 1) (hq : ‖q‖ < 1)
    (d r : ℕ) (hd : d ≠ 0) :
    factors s q d r = ∏ i : Fin 5, factors s q (5 * d) (d * i.val + r) := by
  let e := (Equiv.prodComm (Fin 5) ℕ).trans (Nat.divModEquiv 5).symm
  have hp := e.hasProd_iff.mpr (factors_prod hs hq d r hd)
  refine (hp.prod_fiberwise (g := fun i : Fin 5 ↦ factors s q (5 * d) (d * i.val + r))
    (fun i ↦ ?_)).unique (hasProd_fintype _)
  apply (factors_prod hs hq _ _ (Nat.mul_ne_zero (by decide) hd)).congr_fun
  intro n
  change 1 + s * q ^ (d * (n * 5 + i.val) + r) = _
  congr 3
  ring

private lemma factors_pow (s q : ℂ) (k d r : ℕ) :
    factors s (q ^ k) d r = factors s q (k * d) (k * r) := by
  simp only [factors, ← pow_mul, Nat.mul_add, Nat.mul_assoc]

private lemma theta_factors {s q : ℂ} (hs : s = 1 ∨ s = -1) (hq : q ≠ 0) (h : ‖q‖ < 1)
    (a b : ℕ) (hd : a + b ≠ 0) :
    ramanujanThetaRaw (s * q ^ a) (s * q ^ b) =
      E q (a + b) * factors s q (a + b) a * factors s q (a + b) b := by
  have hs₀ : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hsn : ‖s‖ ≤ 1 := by rcases hs with rfl | rfl <;> simp
  have hs₂ : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  let A := s * q ^ a
  let B := s * q ^ b
  have hA : A ≠ 0 := mul_ne_zero hs₀ (pow_ne_zero _ hq)
  have hAB : A * B = q ^ (a + b) := by
    dsimp [A, B]
    rw [mul_mul_mul_comm, hs₂, one_mul, pow_add]
  have hj := jtpHub_hasSum (q ^ (a + b)) (-A) (pow_ne_zero _ hq) (neg_ne_zero.mpr hA)
    (norm_pow_lt h hd)
  have hterm (n : ℤ) : ramanujanThetaTerm A B n = jtpTheta (q ^ (a + b)) (-A) n := by
    have hv : (triangular n : ℤ) = jtpTri n := by
      unfold triangular jtpTri
      apply Int.toNat_of_nonneg
      apply Int.ediv_nonneg _ (by decide)
      rcases le_or_gt 1 n with hn | hn
      · exact mul_nonneg (by omega) (by omega)
      · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    have hu : (triangular (-n) : ℤ) = jtpTri n + n := by
      have h₁ := twice_triangular (-n)
      have h₂ := twice_triangular n
      rw [← hv]
      linarith
    have he : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_zpow]; norm_num
    rw [term_eq, ← zpow_natCast A, hu, zpow_add₀ hA, jtpTheta, ← hAB,
      show -A = (-1) * A by ring, mul_zpow (-1) A, ← hv]
    simp only [zpow_natCast, mul_pow]
    linear_combination -(A ^ triangular n * B ^ triangular n * A ^ n) * he
  rw [ramanujanThetaRaw, tsum_congr hterm, hj.tsum_eq]
  have hp := ((hasProd_eulerFunction (norm_pow_lt h hd)).mul
    (factors_prod hsn h _ a hd)).mul (factors_prod hsn h _ b hd)
  apply (hp.congr_fun (g := jtpHub (q ^ (a + b)) (-A)) _).tprod_eq
  intro n
  dsimp [jtpHub, A]
  rw [inv_neg, neg_mul, sub_neg_eq_add, neg_mul, sub_neg_eq_add, pow_succ]
  rcases hs with rfl | rfl <;> field_simp <;> ring

/-- The theta factors for the two pairs of nonzero residue classes modulo five. -/
private noncomputable abbrev U (s q : ℂ) :=
  ramanujanThetaRaw (s * q ^ 1) (s * q ^ 4) * ramanujanThetaRaw (s * q ^ 2) (s * q ^ 3)

/-- The theta factors for the two pairs of invertible residue classes modulo ten. -/
private noncomputable abbrev V (s q : ℂ) :=
  ramanujanThetaRaw (s * q ^ 1) (s * q ^ 9) * ramanujanThetaRaw (s * q ^ 3) (s * q ^ 7)

private lemma U_prod {s q : ℂ} (hs : s = 1 ∨ s = -1) (hq : q ≠ 0) (h : ‖q‖ < 1) :
    U s q * factors s (q ^ 5) 1 1 = E q 5 ^ 2 * factors s q 1 1 := by
  have hsn : ‖s‖ ≤ 1 := by rcases hs with rfl | rfl <;> simp
  rw [U, theta_factors hs hq h 1 4 (by decide), theta_factors hs hq h 2 3 (by decide),
    factors_pow, factors_split hsn h 1 1 one_ne_zero]
  simp [Fin.prod_univ_succ]
  ring

private lemma V_prod {s q : ℂ} (hs : s = 1 ∨ s = -1) (hq : q ≠ 0) (h : ‖q‖ < 1) :
    V s q * factors s (q ^ 5) 2 1 = E q 10 ^ 2 * factors s q 2 1 := by
  have hsn : ‖s‖ ≤ 1 := by rcases hs with rfl | rfl <;> simp
  rw [V, theta_factors hs hq h 1 9 (by decide), theta_factors hs hq h 3 7 (by decide),
    factors_pow, factors_split hsn h 2 1 two_ne_zero]
  simp [Fin.prod_univ_succ]
  ring

private lemma all_minus {q : ℂ} (h : ‖q‖ < 1) :
    factors (-1) q 1 1 = E q 1 := by
  simpa [factors, E, sub_eq_add_neg] using (hasProd_eulerFunction h).tprod_eq

private lemma all_plus {q : ℂ} (h : ‖q‖ < 1) :
    factors 1 q 1 1 = E q 2 / E q 1 := by
  simpa [factors, E] using
    (one_div_f1_pow_four_eight_twelve_two_dissection.plus_prod h).tprod_eq

private lemma odd_minus {q : ℂ} (h : ‖q‖ < 1) :
    factors (-1) q 2 1 = E q 1 / E q 2 := by
  simpa [factors, E, sub_eq_add_neg] using (odd_minus_prod h).tprod_eq

private lemma odd_plus {q : ℂ} (h : ‖q‖ < 1) :
    factors 1 q 2 1 = E q 2 ^ 2 / (E q 1 * E q 4) := by
  simpa [factors, E] using (odd_plus_prod h).tprod_eq

private lemma E_pow (q : ℂ) (k d : ℕ) : E (q ^ k) d = E q (k * d) := by
  simp only [E, pow_mul]

private lemma U_minus {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    U (-1) q = E q 1 * E q 5 := by
  have hp := U_prod (.inr rfl) hq h
  rw [all_minus (norm_pow_lt h (by decide)), all_minus h, E_pow] at hp
  exact mul_right_cancel₀ (E_ne h 5) (by linear_combination hp)

private lemma U_plus {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    U 1 q = E q 5 ^ 3 * E q 2 / (E q 1 * E q 10) := by
  have hp := U_prod (.inl rfl) hq h
  rw [all_plus (norm_pow_lt h (by decide)), all_plus h] at hp
  simp only [E_pow, Nat.reduceMul] at hp
  field_simp [E_ne h 1, E_ne h 5, E_ne h 10] at hp ⊢
  linear_combination hp

private lemma V_minus {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    V (-1) q = E q 1 * E q 10 ^ 3 / (E q 2 * E q 5) := by
  have hp := V_prod (.inr rfl) hq h
  rw [odd_minus (norm_pow_lt h (by decide)), odd_minus h] at hp
  simp only [E_pow, Nat.reduceMul] at hp
  field_simp [E_ne h 2, E_ne h 5, E_ne h 10] at hp ⊢
  linear_combination hp

private lemma V_plus {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    V 1 q = E q 2 ^ 2 * E q 5 * E q 20 / (E q 1 * E q 4) := by
  have hp := V_prod (.inl rfl) hq h
  rw [odd_plus (norm_pow_lt h (by decide)), odd_plus h] at hp
  simp only [E_pow, Nat.reduceMul] at hp
  field_simp [E_ne h 1, E_ne h 4, E_ne h 5, E_ne h 20] at hp ⊢
  exact mul_right_cancel₀ (pow_ne_zero 2 (E_ne h 10)) (by linear_combination hp)

/-- Theta addition with first argument `s*q` and ratios `q^i`, `q^j`.
Changing the sign of all four parameters changes only the second summand. -/
private lemma theta_pair {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) (i j : ℕ)
    (s : ℂ) (hs : s = 1 ∨ s = -1) :
    ramanujanThetaRaw (s * q) (s * q ^ (1 + i + j)) *
      ramanujanThetaRaw (s * q ^ (1 + i)) (s * q ^ (1 + j)) =
    ramanujanThetaRaw (q ^ (2 + j)) (q ^ (2 + 2 * i + j)) *
      ramanujanThetaRaw (q ^ (2 + i)) (q ^ (2 + i + 2 * j)) +
      s * q * ramanujanThetaRaw (q ^ i) (q ^ (4 + i + 2 * j)) *
        ramanujanThetaRaw (q ^ j) (q ^ (4 + 2 * i + j)) := by
  have sn : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hp : s * q * (s * q ^ (1 + i + j)) = q ^ (2 + i + j) := by
    rcases hs with rfl | rfl <;> simp [pow_add] <;> ring
  rw [ramanujanTheta_mul_of_mul_eq (mul_ne_zero sn hq) (hp ▸ norm_pow_lt h (by omega))
    (c := s * q ^ (1 + i)) (d := s * q ^ (1 + j)) (by simp [pow_add]; ring)]
  rcases hs with rfl | rfl <;>
    simp [pow_add, pow_mul, mul_div_cancel_left₀, hq] <;> ring_nf

private lemma U_difference {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    U 1 q ^ 2 - U (-1) q ^ 2 = 4 * q * V 1 q * U 1 (q ^ 2) := by
  have hp := theta_pair hq h 1 2 1 (.inl rfl)
  have hm := theta_pair hq h 1 2 (-1) (.inr rfl)
  simp only [U, V, one_mul, neg_one_mul, ← pow_mul, Nat.reduceAdd, Nat.reduceMul, pow_one]
    at hp hm ⊢
  rw [hp, hm]
  ring

private lemma V_dissection {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1)
    (s : ℂ) (hs : s = 1 ∨ s = -1) :
    V s q = U 1 (q ^ 4) + s * q * V 1 (q ^ 2) := by
  have ht := theta_pair hq h 2 6 s hs
  simp only [U, V, one_mul, ← pow_mul, Nat.reduceAdd, Nat.reduceMul, pow_one] at ht ⊢
  linear_combination ht

private lemma level_five {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    E q 2 ^ 2 * E q 5 ^ 5 =
      E q 1 ^ 4 * E q 5 * E q 10 ^ 2 + 4 * q * E q 1 * E q 2 * E q 10 ^ 5 := by
  have he := U_difference hq h
  rw [U_plus hq h, U_minus hq h, V_plus hq h,
    U_plus (pow_ne_zero _ hq) (norm_pow_lt h two_ne_zero)] at he
  simp only [E_pow, Nat.reduceMul] at he
  field_simp [E_ne h 1, E_ne h 2, E_ne h 4, E_ne h 10, E_ne h 20] at he
  apply mul_right_cancel₀ (E_ne h 5)
  linear_combination he

open Function.Periodic ModularForm

private lemma qParam_level (z : ℂ) (d : ℕ) (l : ℝ) :
    qParam l (d * z) = qParam l z ^ d := by
  rw [qParam, qParam, ← Complex.exp_nat_mul]
  congr 1
  ring

private lemma qParam_twenty_four (z : ℂ) : qParam 24 z ^ 24 = qParam 1 z := by
  rw [qParam, qParam, ← Complex.exp_nat_mul]
  congr 1
  norm_num
  ring

private lemma eta_level {z : ℂ} (hz : 0 < z.im) (d : ℕ) (hd : d ≠ 0 := by decide) :
    eta (d * z) = qParam 24 z ^ d * E (qParam 1 z) d := by
  rw [eta, qParam_level, E, eulerFunction_eq_tprod (norm_pow_lt (norm_qParam_lt_one one_pos hz) hd)]
  simp only [eta_q, qParam_level]

private lemma eta_relation {z : ℂ} (hz : 0 < z.im) :
    eta (2 * z) ^ 2 * eta (5 * z) ^ 5 =
      eta z ^ 4 * eta (5 * z) * eta (10 * z) ^ 2 + 4 * eta z * eta (2 * z) * eta (10 * z) ^ 5 := by
  have he := level_five (qParam_ne_zero (h := 1) z) (norm_qParam_lt_one one_pos hz)
  have e1 := eta_level hz 1
  norm_num at e1
  have e2 := eta_level hz 2
  have e5 := eta_level hz 5
  have e10 := eta_level hz 10
  norm_num only [Nat.cast_ofNat] at e2 e5 e10
  rw [e2, e5, e10, e1]
  generalize ht : qParam 24 z = t at *
  have hq : qParam 1 z = t ^ 24 := ht ▸ (qParam_twenty_four z).symm
  rw [hq] at he ⊢
  linear_combination t ^ 29 * he

open Complex in
private lemma sqrt_level (z : ℂ) (k : ℕ) :
    sqrt (k * z) = (Real.sqrt k : ℂ) * sqrt z := by
  rw [sqrt, mul_cpow (by simpa only [natCast_arg, zero_add] using
    (show z.arg ∈ Set.Ioc (-Real.pi) Real.pi from ⟨neg_pi_lt_arg _, arg_le_pi _⟩))]
  congr 1
  rw [Real.sqrt_eq_rpow, ofReal_cpow (by positivity)]
  norm_num

/-- Reverse the levels by applying the eta transformation to the nome of `-1/(10z)`. -/
private lemma dual_eta_relation {z : ℂ} (hz : 0 < z.im) :
    eta (5 * z) ^ 2 * eta (2 * z) ^ 5 =
      eta z ^ 5 * eta (5 * z) * eta (10 * z) +
        5 * eta z ^ 2 * eta (2 * z) * eta (10 * z) ^ 4 := by
  let w := -1 / (10 * z)
  have hz₀ : z ≠ 0 := by rintro rfl; simp at hz
  let M := (Complex.sqrt Complex.I)⁻¹ * Complex.sqrt z
  have hM : M ≠ 0 := by simp [M, Complex.sqrt, hz₀]
  have trans (k d : ℕ) (hk : 0 < k) (hkd : k * d = 10) :
      eta (d * w) = M * (Real.sqrt k : ℂ) * eta (k * z) := by
    have hpos : 0 < ((k : ℂ) * z).im := by simpa using mul_pos (Nat.cast_pos.mpr hk) hz
    have ht := eta_comp_eq_csqrt_I_inv hpos
    change eta (-1 / (k * z)) = _ at ht
    rw [show (d : ℂ) * w = -1 / (k * z) by
      have he : (k : ℂ) * d = 10 := by exact_mod_cast hkd
      dsimp [w]
      have hd₀ : (d : ℂ) ≠ 0 := by
        rintro hd
        rw [hd, mul_zero] at he
        norm_num at he
      rw [← he]
      have hk₀ : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp]
    rw [ht]
    change (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt (k * z) * eta _) = _
    rw [sqrt_level]
    ring
  have hw : 0 < w.im := by
    have hp : 0 < ((10 : ℂ) * z).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 10) hz
    simpa [w, neg_div] using (UpperHalfPlane.mk _ hp).im_inv_neg_coe_pos
  have h := eta_relation hw
  have h1 := trans 10 1 (by decide) (by decide)
  have h2 := trans 5 2 (by decide) (by decide)
  have h5 := trans 2 5 (by decide) (by decide)
  have h10 := trans 1 10 (by decide) (by decide)
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul, Real.sqrt_one, Complex.ofReal_one,
    mul_one] at h1 h2 h5 h10
  rw [h1, h2, h5, h10] at h
  rw [show Real.sqrt 10 = Real.sqrt 2 * Real.sqrt 5 by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num, Complex.ofReal_mul] at h
  have s2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by norm_cast; norm_num
  have s5 : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by norm_cast; norm_num
  generalize (Real.sqrt 2 : ℂ) = a at h s2
  generalize (Real.sqrt 5 : ℂ) = b at h s5
  have ha : a ≠ 0 := by rintro rfl; norm_num at s2
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num : (20 : ℂ) ≠ 0) ha)
    (pow_ne_zero 7 hM))
  linear_combination (norm := (ring_nf; grind)) h

private lemma dual_level_five {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    E q 5 ^ 2 * E q 2 ^ 5 =
      E q 1 ^ 5 * E q 5 * E q 10 + 5 * q * E q 1 ^ 2 * E q 2 * E q 10 ^ 4 := by
  let z := invQParam 1 q
  have hz : 0 < z.im := im_invQParam_pos_of_norm_lt_one one_pos h hq
  have hh := dual_eta_relation hz
  have e1 := eta_level hz 1
  have e2 := eta_level hz 2
  have e5 := eta_level hz 5
  have e10 := eta_level hz 10
  norm_num only [Nat.cast_ofNat, Nat.cast_one, one_mul, pow_one] at e1 e2 e5 e10
  rw [e1, e2, e5, e10] at hh
  have hnome : qParam 1 z = q := qParam_right_inv one_ne_zero hq
  rw [hnome] at hh
  apply mul_left_cancel₀ (pow_ne_zero 20 (qParam_ne_zero (h := 24) z))
  linear_combination hh +
    5 * qParam 24 z ^ 20 * E q 1 ^ 2 * E q 2 * E q 10 ^ 4 *
      ((qParam_twenty_four z).trans hnome)

/-- Expand the fourth power of the two-term dissection of the level-five quotient.
Here `a, b, c, d` are the products at levels 1, 2, 4, 8 and `e, f, g, h` at 5, 10, 20, 40.
Multiplying the quotient by its value at `-q` gives the difference of squares `K`. -/
private lemma combine {q a b c d e f g h : ℂ}
    (hq : q ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (he : e ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (plus : b ^ 2 * e * g / (a * c) =
      g ^ 3 * d / (c * h) + 1 * q * (c ^ 2 * f * h / (b * d)))
    (minus : a * f ^ 3 / (b * e) =
      g ^ 3 * d / (c * h) + -1 * q * (c ^ 2 * f * h / (b * d)))
    (level : b ^ 2 * e ^ 5 = a ^ 4 * e * f ^ 2 + 4 * q * a * b * f ^ 5)
    (level₂ : c ^ 2 * f ^ 5 = b ^ 4 * f * g ^ 2 + 4 * q ^ 2 * b * c * g ^ 5)
    (dual₂ : f ^ 2 * c ^ 5 = b ^ 5 * f * g + 5 * q ^ 2 * b ^ 2 * c * g ^ 4) :
    b ^ 10 * d ^ 2 * f ^ 3 * g =
      a ^ 3 * b ^ 3 * c ^ 4 * e * d ^ 2 * f ^ 2 * g -
        2 * q * a ^ 3 * b * c ^ 6 * e * d ^ 2 * g ^ 3 +
        5 * q * a ^ 3 * b ^ 2 * c ^ 3 * e * d ^ 2 * f ^ 3 * g ^ 2 +
        2 * q ^ 2 * a ^ 3 * c ^ 9 * e * f * h ^ 2 := by
  let A := d * g ^ 2 / (b ^ 2 * h)
  let B := c ^ 3 * f * h / (b ^ 3 * d * g)
  let K := f ^ 3 * c / (b ^ 3 * g)
  have hz : e / a = A + q * B := by
    dsimp [A, B]
    linear_combination (norm := (field_simp; ring)) c / (b ^ 2 * g) * plus
  have hm : K / (e / a) = A - q * B := by
    dsimp [A, B, K]
    linear_combination (norm := (field_simp; ring)) c / (b ^ 2 * g) * minus
  have hK : K = A ^ 2 - q ^ 2 * B ^ 2 := by
    calc
      K = e / a * (K / (e / a)) := by field_simp
      _ = _ := by rw [hm, hz]; ring
  have hrec : 1 / (a ^ 3 * e) = (b ^ 2 * (e / a) ^ 4 - f ^ 2) / (4 * q * b * f ^ 5) := by
    linear_combination (norm := (field_simp; ring)) -level / (4 * q * a ^ 4 * b * e * f ^ 5)
  have hfour : (e / a) ^ 4 =
      K ^ 2 + 8 * q ^ 2 * A ^ 2 * B ^ 2 + 4 * q * A * B * (K + 2 * q ^ 2 * B ^ 2) := by
    rw [hz, hK]
    ring
  have hsq : b ^ 2 * K ^ 2 = f ^ 2 + 4 * q ^ 2 * c * f * g ^ 3 / b ^ 3 := by
    dsimp [K]
    linear_combination (norm := (field_simp; ring)) f / (b ^ 4 * g ^ 2) * level₂
  have hmix : b ^ 5 * g ^ 2 + 4 * c ^ 5 * f * g = 5 * b * c ^ 2 * f ^ 4 := by
    apply mul_right_cancel₀ hf
    linear_combination 4 * g * dual₂ - 5 * b * level₂
  have hquot : 1 / (a ^ 3 * e) = c ^ 4 / (b ^ 7 * f) -
      2 * q * c ^ 6 * g ^ 2 / (b ^ 9 * f ^ 3) + 5 * q * c ^ 3 * g / b ^ 8 +
      2 * q ^ 2 * c ^ 9 * h ^ 2 / (b ^ 10 * d ^ 2 * f ^ 2 * g) := by
    rw [hrec, hfour, mul_add, mul_add, hsq]
    dsimp [A, B, K]
    linear_combination (norm := (field_simp; ring)) q * c * g / (b ^ 9 * f ^ 4) * hmix
  linear_combination (norm := (field_simp; ring)) a ^ 3 * e * b ^ 10 * d ^ 2 * f ^ 3 * g * hquot

private lemma analytic_dissection {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    E q 2 ^ 10 * E q 8 ^ 2 * E q 10 ^ 3 * E q 20 =
      E q 1 ^ 3 * E q 2 ^ 3 * E q 4 ^ 4 * E q 5 * E q 8 ^ 2 * E q 10 ^ 2 * E q 20
        - 2 * q * E q 1 ^ 3 * E q 2 * E q 4 ^ 6 * E q 5 * E q 8 ^ 2 * E q 20 ^ 3
        + 5 * q * E q 1 ^ 3 * E q 2 ^ 2 * E q 4 ^ 3 * E q 5 * E q 8 ^ 2 * E q 10 ^ 3 *
          E q 20 ^ 2
        + 2 * q ^ 2 * E q 1 ^ 3 * E q 4 ^ 9 * E q 5 * E q 10 * E q 40 ^ 2 := by
  have h₂ := norm_pow_lt h two_ne_zero
  have h₄ := norm_pow_lt h (by decide : (4 : ℕ) ≠ 0)
  have hp := V_dissection hq h 1 (.inl rfl)
  have hm := V_dissection hq h (-1) (.inr rfl)
  rw [V_plus hq h] at hp
  rw [V_minus hq h] at hm
  rw [U_plus (pow_ne_zero _ hq) h₄, V_plus (pow_ne_zero _ hq) h₂] at hp hm
  have hl := level_five (pow_ne_zero _ hq) h₂
  have hj := dual_level_five (pow_ne_zero _ hq) h₂
  simp only [E_pow, Nat.reduceMul] at hp hm hl hj
  exact combine hq (E_ne h 1) (E_ne h 2) (E_ne h 4) (E_ne h 8) (E_ne h 5)
    (E_ne h 10) (E_ne h 20) (E_ne h 40) hp hm (level_five hq h) hl hj

open one_div_f1_pow_four_eight_twelve_two_dissection

private lemma represents_sub {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g) : Represents (F - G) (fun q ↦ f q - g q) := by
  intro τ
  simpa [sub_mul] using (hf τ).sub (hg τ)

end one_div_f1_cube_f5_two_dissection

local notation "𝔣" => qEulerProduct

open one_div_f1_cube_f5_two_dissection one_div_f1_pow_four_eight_twelve_two_dissection in
/-- **A 2-dissection of the reciprocal Euler product of levels 1 and 5.** Let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ in the ring of integer power series in $q$. Then
$$f_2^{10} f_8^2 f_{10}^3 f_{20} = f_1^3 f_2^3 f_4^4 f_5 f_8^2 f_{10}^2 f_{20} -
2q f_1^3 f_2 f_4^6 f_5 f_8^2 f_{20}^3 + 5q f_1^3 f_2^2 f_4^3 f_5 f_8^2 f_{10}^3 f_{20}^2 +
2q^2 f_1^3 f_4^9 f_5 f_{10} f_{40}^2.$$

Dividing both sides by $f_1^3 f_5 f_2^{10} f_8^2 f_{10}^3 f_{20}$ gives the form in the source,
$1/(f_1^3 f_5) = f_4^4/(f_2^7 f_{10}) - 2q f_4^6 f_{20}^2/(f_2^9 f_{10}^3) +
5q f_4^3 f_{20}/f_2^8 + 2q^2 f_4^9 f_{40}^2/(f_2^{10} f_8^2 f_{10}^2 f_{20})$.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Lemma 4, eq. (15)
(`integers-2025-A17-lem-4`). -/
public theorem one_div_f1_cube_f5_two_dissection :
    𝔣 2 ^ 10 * 𝔣 8 ^ 2 * 𝔣 10 ^ 3 * 𝔣 20 =
      𝔣 1 ^ 3 * 𝔣 2 ^ 3 * 𝔣 4 ^ 4 * 𝔣 5 * 𝔣 8 ^ 2 * 𝔣 10 ^ 2 * 𝔣 20
        - 2 * X * 𝔣 1 ^ 3 * 𝔣 2 * 𝔣 4 ^ 6 * 𝔣 5 * 𝔣 8 ^ 2 * 𝔣 20 ^ 3
        + 5 * X * 𝔣 1 ^ 3 * 𝔣 2 ^ 2 * 𝔣 4 ^ 3 * 𝔣 5 * 𝔣 8 ^ 2 * 𝔣 10 ^ 3 * 𝔣 20 ^ 2
        + 2 * X ^ 2 * 𝔣 1 ^ 3 * 𝔣 4 ^ 9 * 𝔣 5 * 𝔣 10 * 𝔣 40 ^ 2 := by
  have h2 : Represents 2 (fun _ ↦ 2) := by simpa using represents_const 2
  have h5 : Represents 5 (fun _ ↦ 5) := by simpa using represents_const 5
  have f (k : ℕ) (hk : k ≠ 0 := by decide) := represents_euler k hk
  have lhs := ((((f 2).pow 10).mul ((f 8).pow 2)).mul ((f 10).pow 3)).mul (f 20)
  have common := ((f 1).pow 3).mul ((f 2).pow 3)
  have main := (((common.mul ((f 4).pow 4)).mul (f 5)).mul ((f 8).pow 2)).mul ((f 10).pow 2)
  have linear := (h2.mul represents_X).mul ((f 1).pow 3)
  have negTerm := (((linear.mul (f 2)).mul ((f 4).pow 6)).mul (f 5)).mul ((f 8).pow 2)
  have linear' := ((h5.mul represents_X).mul ((f 1).pow 3)).mul ((f 2).pow 2)
  have posTerm := (((linear'.mul ((f 4).pow 3)).mul (f 5)).mul ((f 8).pow 2)).mul ((f 10).pow 3)
  have quad := (((h2.mul (represents_X.pow 2)).mul ((f 1).pow 3)).mul ((f 4).pow 9)).mul (f 5)
  have rhs := ((represents_sub (main.mul (f 20)) (negTerm.mul ((f 20).pow 3))).add
    (posTerm.mul ((f 20).pow 2))).add ((quad.mul (f 10)).mul ((f 40).pow 2))
  exact lhs.eq_of_eval rhs (fun _ ↦ one_div_f1_cube_f5_two_dissection.analytic_dissection)

end MetaMathlibExt
