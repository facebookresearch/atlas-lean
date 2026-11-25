/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The length of a dense ternary coefficient sequence

We work over `ZMod 3`, where cubing separates the low ternary digits of the two exponents.
For mixed low digits, density forces consecutive coefficients of the quotient product to
be equal or opposite, so multiplying by a linear factor leaves a binomial.
-/

namespace MetaMathlibExt

open Polynomial

private abbrev F := ZMod 3

private noncomputable def signedProduct (c d : ℕ) : F[X] := (X - 1) ^ c * (X + 1) ^ d

private theorem signedProduct_monic (c d : ℕ) : (signedProduct c d).Monic := by
  simpa only [signedProduct, C_1] using ((monic_X_sub_C (1 : F)).pow c).mul
    ((monic_X_add_C (1 : F)).pow d)

private theorem signedProduct_natDegree (c d : ℕ) : (signedProduct c d).natDegree = c + d := by
  have hm : (X - 1 : F[X]).Monic := by simpa using monic_X_sub_C (1 : F)
  have hp : (X + 1 : F[X]).Monic := by simpa using monic_X_add_C (1 : F)
  have dm : (X - 1 : F[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : F)
  have dp : (X + 1 : F[X]).natDegree = 1 := by simp
  rw [signedProduct, (hm.pow c).natDegree_mul (hp.pow d), natDegree_pow, natDegree_pow, dm, dp]
  simp

private theorem signedProduct_coeff_zero (c d : ℕ) : (signedProduct c d).coeff 0 ≠ 0 := by
  simp [signedProduct, coeff_zero_eq_eval_zero]

private theorem signedProduct_coeff_top (c d : ℕ) : (signedProduct c d).coeff (c + d) = 1 := by
  rw [← signedProduct_natDegree, coeff_natDegree, (signedProduct_monic c d).leadingCoeff]

-- Cubing the two linear factors replaces X by X³.
private theorem signedProduct_split (c d r s : ℕ) :
    signedProduct (c * 3 + r) (d * 3 + s) =
      signedProduct r s * expand F 3 (signedProduct c d) := by
  have hm : (X - 1 : F[X]) ^ 3 = X ^ 3 - 1 := by rw [sub_pow_char (p := 3), one_pow]
  have hp : (X + 1 : F[X]) ^ 3 = X ^ 3 + 1 := by rw [add_pow_char _ _ 3, one_pow]
  simp only [signedProduct, map_mul, map_pow, map_sub, map_add, map_one, expand_X,
    pow_add, pow_mul', ← hm, ← hp]
  ring

private noncomputable def digitPoly (a b c d e : F) : F[X] :=
  C a + C b * X + C c * X ^ 2 + C d * X ^ 3 + C e * X ^ 4

private theorem coeff_shift_expand (q : F[X]) (m n : ℕ) :
    (X ^ m * expand F 3 q).coeff n =
      if m ≤ n ∧ 3 ∣ n - m then q.coeff ((n - m) / 3) else 0 := by
  by_cases h : m ≤ n
  · conv_lhs => rw [← Nat.sub_add_cancel h]
    rw [coeff_X_pow_mul, coeff_expand (by decide : 0 < 3)]
    simp [h]
  · have hz : (X ^ m * expand F 3 q).coeff n = 0 := by
      rw [coeff_mul]
      apply Finset.sum_eq_zero
      intro ij hij
      have he := Finset.mem_antidiagonal.mp hij
      simp [coeff_X_pow, show ij.1 ≠ m by omega]
    simp [h, hz]

private def precedingCoeff (q : F[X]) (j : ℕ) : F :=
  if j = 0 then 0 else q.coeff (j - 1)

-- Each block of three coefficients receives a contribution from the corresponding
-- coefficient of q, and (for residual terms of degree 3 or 4) from its predecessor.
private theorem digitPoly_coeffs (q : F[X]) (a b c d e : F) (j : ℕ) :
    ((digitPoly a b c d e * expand F 3 q).coeff (j * 3) =
      a * q.coeff j + d * precedingCoeff q j) ∧
    ((digitPoly a b c d e * expand F 3 q).coeff (j * 3 + 1) =
      b * q.coeff j + e * precedingCoeff q j) ∧
    ((digitPoly a b c d e * expand F 3 q).coeff (j * 3 + 2) = c * q.coeff j) := by
  have same (n : ℕ) :
      (X ^ n * expand F 3 q).coeff (j * 3 + n) = q.coeff j := by
    rw [coeff_shift_expand, ite_eq_left ⟨by omega, by omega⟩, show (j * 3 + n - n) / 3 = j by omega]
  have prev (n : ℕ) :
      (X ^ (n + 3) * expand F 3 q).coeff (j * 3 + n) = precedingCoeff q j := by
    rw [coeff_shift_expand]
    by_cases hj : j = 0
    · simp [precedingCoeff, hj]
    · rw [ite_eq_left ⟨by omega, by omega⟩, show (j * 3 + n - (n + 3)) / 3 = j - 1 by omega]
      simp [precedingCoeff, hj]
  have other (m n : ℕ) (hn : n ≤ 2) (hne : m % 3 ≠ n) :
      (X ^ m * expand F 3 q).coeff (j * 3 + n) = 0 := by
    rw [coeff_shift_expand, ite_eq_right (by omega)]
  have h0 : (expand F 3 q).coeff (j * 3) = q.coeff j := coeff_expand_mul (by decide) q j
  have h1 : (expand F 3 q).coeff (j * 3 + 1) = 0 := by
    rw [coeff_expand (by decide), ite_eq_right (by omega)]
  have h2 : (expand F 3 q).coeff (j * 3 + 2) = 0 := by
    rw [coeff_expand (by decide), ite_eq_right (by omega)]
  have hx (n : ℕ) : (X * expand F 3 q).coeff n = (X ^ 1 * expand F 3 q).coeff n := by simp
  constructor
  · have h10 := other 1 0 (by decide) (by decide)
    have h20 := other 2 0 (by decide) (by decide)
    have h40 := other 4 0 (by decide) (by decide)
    have h30 := prev 0
    simp only [Nat.add_zero] at h10 h20 h40 h30
    simp only [digitPoly, add_mul, mul_assoc, coeff_add, coeff_C_mul, hx, h0,
      h10, h20, h30, h40, mul_zero, add_zero]
  constructor
  · simp only [digitPoly, add_mul, mul_assoc, coeff_add, coeff_C_mul, hx, h1, same 1,
      other 2 1 (by decide) (by decide), other 3 1 (by decide) (by decide),
      prev 1, mul_zero, zero_add, add_zero]
  · simp only [digitPoly, add_mul, mul_assoc, coeff_add, coeff_C_mul, hx, h2, same 2,
      other 1 2 (by decide) (by decide), other 3 2 (by decide) (by decide),
      other 4 2 (by decide) (by decide), mul_zero, zero_add, add_zero]

private theorem digit00 : signedProduct 0 0 = digitPoly 1 0 0 0 0 := by
  simp [signedProduct, digitPoly]

private theorem digit10 : signedProduct 1 0 = digitPoly (-1) 1 0 0 0 := by
  simp [signedProduct, digitPoly, sub_eq_add_neg, add_comm]

private theorem digit01 : signedProduct 0 1 = digitPoly 1 1 0 0 0 := by
  simp [signedProduct, digitPoly, add_comm]

private theorem digit20 : signedProduct 2 0 = digitPoly 1 1 1 0 0 := by
  have h : (2 : F[X]) = -1 := by
    rw [← C_1 (R := F), ← map_neg, ← map_ofNat C]; congr 1
  simp [signedProduct, digitPoly]
  linear_combination -(X : F[X]) * h

private theorem digit02 : signedProduct 0 2 = digitPoly 1 (-1) 1 0 0 := by
  have h : (2 : F[X]) = -1 := by
    rw [← C_1 (R := F), ← map_neg, ← map_ofNat C]; congr 1
  simp [signedProduct, digitPoly]
  linear_combination (X : F[X]) * h

private theorem digit11 : signedProduct 1 1 = digitPoly (-1) 0 1 0 0 := by
  simp [signedProduct, digitPoly]
  ring

private theorem digit12 : signedProduct 1 2 = digitPoly (-1) (-1) 1 1 0 := by
  simp [signedProduct, digitPoly]
  ring

private theorem digit21 : signedProduct 2 1 = digitPoly 1 (-1) (-1) 1 0 := by
  simp [signedProduct, digitPoly]
  ring

private theorem digit22 : signedProduct 2 2 = digitPoly 1 0 1 0 1 := by
  have h : (2 : F[X]) = -1 := by
    rw [← C_1 (R := F), ← map_neg, ← map_ofNat C]; congr 1
  simp [signedProduct, digitPoly]
  linear_combination -(X : F[X]) ^ 2 * h

private theorem ternary_split (c d : ℕ) :
    signedProduct c d =
      signedProduct (c % 3) (d % 3) * expand F 3 (signedProduct (c / 3) (d / 3)) := by
  simpa only [show c / 3 * 3 + c % 3 = c by omega, show d / 3 * 3 + d % 3 = d by omega] using
    signedProduct_split (c / 3) (d / 3) (c % 3) (d % 3)

-- The first two nonconstant coefficients can both vanish only for the zero digit pair.
private theorem zero_digits_of_coeffs (q : F[X]) (hq : q.coeff 0 ≠ 0) {r s : ℕ}
    (hr : r < 3) (hs : s < 3)
    (h₁ : (signedProduct r s * expand F 3 q).coeff 1 = 0)
    (h₂ : (signedProduct r s * expand F 3 q).coeff 2 = 0) : r = 0 ∧ s = 0 := by
  have low₁ (a b c d e : F) :
      (digitPoly a b c d e * expand F 3 q).coeff 1 = b * q.coeff 0 := by
    simpa [precedingCoeff] using (digitPoly_coeffs q a b c d e 0).2.1
  have low₂ (a b c d e : F) :
      (digitPoly a b c d e * expand F 3 q).coeff 2 = c * q.coeff 0 :=
    (digitPoly_coeffs q a b c d e 0).2.2
  interval_cases r <;> interval_cases s
  all_goals first
    | exact ⟨rfl, rfl⟩
    | simp only [digit01, digit02, digit10, digit11, digit12, digit20, digit21, digit22,
        low₁, low₂] at h₁ h₂
      simp_all

-- If a nonconstant signed product is a binomial of degree > 2, the previous lemma
-- forces both exponents to be multiples of 3. Undo the expansion and induct.
private theorem binomial_length (n c d : ℕ) (k : F) (hn : 0 < n) (hcd : c + d = n)
    (hp : signedProduct c d = X ^ n + C k) : ∃ j : ℕ, n = 3 ^ j ∨ n = 2 * 3 ^ j := by
  induction n using Nat.strong_induction_on generalizing c d with
  | ind n ih =>
    by_cases h₁ : n = 1
    · exact ⟨0, Or.inl (by simpa using h₁)⟩
    by_cases h₂ : n = 2
    · exact ⟨0, Or.inr (by simpa using h₂)⟩
    let q := signedProduct (c / 3) (d / 3)
    have hz (t : ℕ) (ht : 0 < t) (htn : t < n) :
        (signedProduct (c % 3) (d % 3) * expand F 3 q).coeff t = 0 := by
      rw [← ternary_split c d, hp]
      simp [coeff_X_pow, coeff_C, ht.ne', htn.ne]
    obtain ⟨hc, hd⟩ := zero_digits_of_coeffs q (signedProduct_coeff_zero _ _)
      (by omega : c % 3 < 3) (by omega : d % 3 < 3) (hz 1 (by omega) (by omega))
      (hz 2 (by omega) (by omega))
    let m := c / 3 + d / 3
    have hm : 3 * m = n := by dsimp [m]; omega
    have hq : q = X ^ m + C k := by
      apply expand_injective (R := F) (by decide : 0 < 3)
      calc
        expand F 3 q = signedProduct c d := by
          rw [ternary_split c d, hc, hd]
          simp [signedProduct, q]
        _ = X ^ n + C k := hp
        _ = expand F 3 (X ^ m + C k) := by
          rw [map_add, map_pow, expand_X, expand_C, ← pow_mul, hm]
    obtain ⟨j, hj | hj⟩ := ih m (by omega) (c / 3) (d / 3) (by omega) rfl hq
    · exact ⟨j + 1, Or.inl (by rw [← hm, hj, pow_succ, Nat.mul_comm])⟩
    · exact ⟨j + 1, Or.inr (by rw [← hm, hj, pow_succ]; omega)⟩

-- For nonzero a, x and y over F₃, either y + a*x or y - a*x must vanish.
private theorem other_sign_vanishes : ∀ a x y : F,
    a ≠ 0 → x ≠ 0 → y ≠ 0 → y + a * x ≠ 0 → y - a * x = 0 := by decide

private theorem mixed_length (c d : ℕ) (a b : F) (ha : a ≠ 0)
    (h : ∀ k ≤ (c + d) * 3 + 3,
      (digitPoly a (-1) b 1 0 * expand F 3 (signedProduct c d)).coeff k ≠ 0) :
    ∃ j : ℕ, c + d + 1 = 3 ^ j ∨ c + d + 1 = 2 * 3 ^ j := by
  let q := signedProduct c d
  let n := c + d
  have hd (j : ℕ) (hj : j ≤ n) : q.coeff j ≠ 0 := by
    have h₁ := h (j * 3 + 1) (by omega)
    rw [(digitPoly_coeffs q a (-1) b 1 0 j).2.1] at h₁
    simpa using h₁
  have ht (j : ℕ) (hj : j < n) : q.coeff j - a * q.coeff (j + 1) = 0 := by
    apply other_sign_vanishes a _ _ ha (hd _ (by omega)) (hd _ (by omega))
    have h₀ := h ((j + 1) * 3) (by omega)
    rw [(digitPoly_coeffs q a (-1) b 1 0 (j + 1)).1] at h₀
    simpa [precedingCoeff, add_comm] using h₀
  let k := ((X - C a) * q).coeff 0
  have he : (X - C a) * q = X ^ (n + 1) + C k := by
    ext j
    cases j with
    | zero => simp [coeff_X_pow, k]
    | succ j =>
      simp only [coeff_X_sub_C_mul, coeff_add, coeff_X_pow, coeff_C, Nat.succ_ne_zero, ite_false,
        add_zero, Nat.succ.injEq]
      rcases lt_trichotomy j n with hj | rfl | hj
      · simp [ht j hj, hj.ne]
      · rw [ite_eq_left rfl, signedProduct_coeff_top, coeff_eq_zero_of_natDegree_lt]
        · simp
        · rw [signedProduct_natDegree]; omega
      · have hz (i : ℕ) (hi : n < i) : q.coeff i = 0 :=
          coeff_eq_zero_of_natDegree_lt (by simpa [q, n, signedProduct_natDegree] using hi)
        simp [hz j hj, hz (j + 1) (by omega), hj.ne']
  have ha' : a = 1 ∨ a = -1 := (by decide : ∀ a : F, a ≠ 0 → a = 1 ∨ a = -1) a ha
  rcases ha' with rfl | rfl
  · apply binomial_length (n + 1) (c + 1) d k (by omega) (by omega)
    convert he using 1
    simp only [q, signedProduct, pow_succ, C_1]
    ac_rfl
  · apply binomial_length (n + 1) c (d + 1) k (by omega) (by omega)
    convert he using 1
    simp only [q, signedProduct, pow_succ, map_neg, C_1, sub_neg_eq_add]
    ac_rfl

private def LengthShape (n : ℕ) : Prop :=
  ∃ i j : ℕ, j < i ∧ (n = 3 ^ j ∨ n = 2 * 3 ^ j ∨ n = 3 ^ i + 3 ^ j ∨ n = 2 * 3 ^ i + 3 ^ j)

private theorem lengthShape_mul_three {n : ℕ} (h : LengthShape n) : LengthShape (n * 3) := by
  obtain ⟨i, j, hij, h⟩ := h
  refine ⟨i + 1, j + 1, by omega, ?_⟩
  rw [pow_succ, pow_succ]
  rcases h with h | h | h | h <;> omega

private theorem lengthShape_mul_three_add_one {n : ℕ} (h : ∃ j : ℕ, n = 3 ^ j ∨ n = 2 * 3 ^ j) :
    LengthShape (n * 3 + 1) := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j + 1, 0, by omega, ?_⟩
  rw [pow_succ, pow_zero]
  rcases hj with hj | hj <;> omega

private theorem lengthShape_of_small {n : ℕ} (h : n = 1 ∨ n = 2) : LengthShape n := by
  rcases h with rfl | rfl
  · exact ⟨1, 0, by decide, Or.inl rfl⟩
  · exact ⟨1, 0, by decide, Or.inr (Or.inl rfl)⟩

-- Strip two low ternary digits. Short residuals leave a gap, quadratic residuals
-- of one sign pass density down to the quotient, and mixed cubics use the binomial lemma.
private theorem lengthShape_of_residual (c d r s : ℕ) (hr : r < 3) (hs : s < 3)
    (hd : ∀ k ≤ (c + d) * 3 + (r + s),
      (signedProduct r s * expand F 3 (signedProduct c d)).coeff k ≠ 0)
    (ih : (∀ k ≤ c + d, (signedProduct c d).coeff k ≠ 0) → LengthShape (c + d + 1)) :
    LengthShape ((c + d) * 3 + (r + s) + 1) := by
  let q := signedProduct c d
  have short (t : ℕ) (ht : t = r + s + 1) (ht' : t ≤ 2)
      (hz : (signedProduct r s * expand F 3 q).coeff t = 0) :
      LengthShape ((c + d) * 3 + (r + s) + 1) := by
    have hgap : ¬ t ≤ (c + d) * 3 + (r + s) := fun hk ↦ hd t hk hz
    exact lengthShape_of_small (by omega)
  have low₁ (a b c d e : F) :
      (digitPoly a b c d e * expand F 3 q).coeff 1 = b * q.coeff 0 := by
    simpa [precedingCoeff] using (digitPoly_coeffs q a b c d e 0).2.1
  have quad (a b : F)
      (h : ∀ k ≤ (c + d) * 3 + 2, (digitPoly a b 1 0 0 * expand F 3 q).coeff k ≠ 0) :
      LengthShape ((c + d) * 3 + 2 + 1) := by
    have hq (j : ℕ) (hj : j ≤ c + d) : q.coeff j ≠ 0 := by
      have hj' := h (j * 3 + 2) (by omega)
      simpa only [(digitPoly_coeffs q a b 1 0 0 j).2.2, one_mul] using hj'
    convert lengthShape_mul_three (ih hq) using 1; omega
  have mixed (a b : F) (ha : a ≠ 0)
      (h : ∀ k ≤ (c + d) * 3 + 3, (digitPoly a (-1) b 1 0 * expand F 3 q).coeff k ≠ 0) :
      LengthShape ((c + d) * 3 + 3 + 1) := by
    convert lengthShape_mul_three_add_one (mixed_length c d a b ha h) using 1; omega
  interval_cases r <;> interval_cases s
  · apply short 1 (by decide) (by decide)
    rw [digit00, low₁, zero_mul]
  · apply short 2 (by decide) (by decide)
    rw [digit01, (digitPoly_coeffs q 1 1 0 0 0 0).2.2, zero_mul]
  · exact quad 1 (-1) (by simpa only [digit02, Nat.zero_add] using hd)
  · apply short 2 (by decide) (by decide)
    rw [digit10, (digitPoly_coeffs q (-1) 1 0 0 0 0).2.2, zero_mul]
  · exact False.elim (hd 1 (by omega) (by rw [digit11, low₁, zero_mul]))
  · exact mixed (-1) 1 (by decide) (by simpa only [digit12] using hd)
  · exact quad 1 1 (by simpa only [digit20, Nat.add_zero] using hd)
  · exact mixed 1 (-1) (by decide) (by simpa only [digit21] using hd)
  · exact False.elim (hd 1 (by omega) (by rw [digit22, low₁, zero_mul]))

private theorem lengthShape_of_dense (n c d : ℕ) (hcd : c + d = n)
    (hd : ∀ k ≤ n, (signedProduct c d).coeff k ≠ 0) : LengthShape (n + 1) := by
  induction n using Nat.strong_induction_on generalizing c d with
  | ind n ih =>
    by_cases hn : n = 0
    · exact lengthShape_of_small (Or.inl (by omega))
    have hsum : (c / 3 + d / 3) * 3 + (c % 3 + d % 3) = n := by omega
    rw [ternary_split] at hd
    rw [← hsum]
    exact lengthShape_of_residual (c / 3) (d / 3) (c % 3) (d % 3) (by omega) (by omega)
      (by rwa [hsum]) (ih _ (by omega) _ _ rfl)

/-- **Hajdu–Tijdeman–Varga theorem on $(x-1)^c (x+1)^d$ modulo $3$.** Let $c$ and $d$ be natural
numbers. If none of the coefficients of $x^0, x^1, \dots, x^{c+d}$ in the integer polynomial
$(x-1)^c (x+1)^d$ is divisible by $3$, then there are natural numbers $i > j$ such that $c + d + 1$
equals $3^j$, $2 \cdot 3^j$, $3^i + 3^j$ or $2 \cdot 3^i + 3^j$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Theorem 10 (`jis-2025-25.3.8-thm-10`), citing Hajdu, Tijdeman, and Varga. -/
public theorem coeff_not_dvd_three_shape (c d : ℕ)
    (h : ∀ k ≤ c + d,
      ¬ (3 : ℤ) ∣ (((Polynomial.X - 1) ^ c * (Polynomial.X + 1) ^ d : Polynomial ℤ)).coeff k) :
    ∃ i j : ℕ, j < i ∧ (c + d + 1 = 3 ^ j ∨ c + d + 1 = 2 * 3 ^ j ∨
      c + d + 1 = 3 ^ i + 3 ^ j ∨ c + d + 1 = 2 * 3 ^ i + 3 ^ j) := by
  have hmap : Polynomial.map (Int.castRingHom F)
      (((X - 1) ^ c * (X + 1) ^ d : ℤ[X])) = signedProduct c d := by
    simp [signedProduct]
  apply lengthShape_of_dense (c + d) c d rfl
  intro k hk hz
  rw [← hmap, coeff_map] at hz
  exact h k hk ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hz)

end MetaMathlibExt
