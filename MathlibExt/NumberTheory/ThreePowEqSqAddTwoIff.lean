/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic
import MathlibExt.NumberTheory.ZsqrtdNegTwoPrimes

/-!
# Solutions of $3^x = y^2 + 2$

Factoring $y^2 + 2$ in $\mathbb{Z}[\sqrt{-2}]$ shows that $y + \sqrt{-2}$ is associated to a
power of $1 + \sqrt{-2}$ or $1 - \sqrt{-2}$; a $2$-adic analysis of the imaginary parts of
those powers leaves only the exponents $1$ and $3$, giving the solutions $(1, 1)$ and $(3, 5)$.
-/

namespace MetaMathlibExt

namespace three_pow_eq_sq_add_two_iff

open Zsqrtd

/-- The element $1 + \sqrt{-2}$ of $\mathbb{Z}[\sqrt{-2}]$, of norm $3$. -/
private def δ : ℤ√(-2 : ℤ) := ⟨1, 1⟩

/-- The real part of $(1 + \sqrt{-2})^n$. -/
private def A (n : ℕ) : ℤ := (δ ^ n).re

/-- The imaginary part of $(1 + \sqrt{-2})^n$. -/
private def B (n : ℕ) : ℤ := (δ ^ n).im

private theorem A_succ (n : ℕ) : A (n + 1) = A n - 2 * B n := by
  simp only [A, B, pow_succ, Zsqrtd.re_mul]
  change (δ ^ n).re * 1 + -2 * (δ ^ n).im * 1 = (δ ^ n).re - 2 * (δ ^ n).im
  ring

private theorem B_succ (n : ℕ) : B (n + 1) = A n + B n := by
  simp only [A, B, pow_succ, Zsqrtd.im_mul]
  change (δ ^ n).re * 1 + (δ ^ n).im * 1 = (δ ^ n).re + (δ ^ n).im
  ring

private theorem norm_eq (n : ℕ) : A n ^ 2 + 2 * B n ^ 2 = 3 ^ n := by
  have hn : Zsqrtd.norm (δ ^ n) = 3 ^ n := by
    rw [Zsqrtd.norm_pow]
    have : Zsqrtd.norm δ = 3 := by decide
    rw [this]
  have hn2 : (δ ^ n).re * (δ ^ n).re - -2 * (δ ^ n).im * (δ ^ n).im = 3 ^ n := hn
  simp only [A, B] at hn2 ⊢
  linear_combination hn2

private theorem add_A (m n : ℕ) : A (m + n) = A m * A n - 2 * B m * B n := by
  simp only [A, B, pow_add, Zsqrtd.re_mul]
  ring

private theorem add_B (m n : ℕ) : B (m + n) = A m * B n + B m * A n := by
  simp only [A, B, pow_add, Zsqrtd.im_mul]

/-- The components of $(1 + \sqrt{-2})^{2^k}$ modulo $2^{k+1}$. -/
private theorem pow2k_cong (k : ℕ) (hk : 2 ≤ k) :
    A (2 ^ k) ≡ 1 [ZMOD (2 : ℤ) ^ (k + 1)] ∧
    B (2 ^ k) ≡ (2 : ℤ) ^ k [ZMOD (2 : ℤ) ^ (k + 1)] := by
  induction k, hk using Nat.le_induction with
  | base =>
    change A 4 ≡ 1 [ZMOD (2 : ℤ) ^ 3] ∧ B 4 ≡ (2 : ℤ) ^ 2 [ZMOD (2 : ℤ) ^ 3]
    refine ⟨?_, ?_⟩ <;> decide
  | succ k hk ih =>
    obtain ⟨hA, hB⟩ := ih
    obtain ⟨s, hs⟩ := Int.modEq_iff_dvd.mp hA
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hB
    have hA1 : A (2 ^ k) = 1 - (2 : ℤ) ^ (k + 1) * s := by omega
    have hB1 : B (2 ^ k) = (2 : ℤ) ^ k - (2 : ℤ) ^ (k + 1) * t := by omega
    have hA2 : A (2 ^ (k + 1)) = A (2 ^ k) ^ 2 - 2 * B (2 ^ k) ^ 2 := by
      rw [pow_succ, mul_two, add_A]; ring
    have hB2 : B (2 ^ (k + 1)) = 2 * A (2 ^ k) * B (2 ^ k) := by
      rw [pow_succ, mul_two, add_B]; ring
    have e1 : (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k := pow_succ' 2 k
    have e4 : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
      conv_lhs => rw [show k = k - 1 + 1 by omega]
      rw [pow_succ']
    refine ⟨?_, ?_⟩
    · rw [Int.modEq_iff_dvd, hA2]
      refine ⟨s - (2 : ℤ) ^ k * s ^ 2 + (2 : ℤ) ^ (k - 1)
        - 2 * (2 : ℤ) ^ k * t + (2 : ℤ) ^ (k + 1) * t ^ 2, ?_⟩
      have hq2 : (2 : ℤ) ^ (k + 1) = 4 * (2 : ℤ) ^ (k - 1) := by rw [e1, e4]; ring
      have hq3 : (2 : ℤ) ^ (k + 1 + 1) = 8 * (2 : ℤ) ^ (k - 1) := by
        rw [show k + 1 + 1 = (k + 1) + 1 from rfl, pow_succ', hq2]; ring
      rw [hA1, hB1, hq2, hq3, e4]
      ring
    · rw [Int.modEq_iff_dvd, hB2]
      refine ⟨t + (2 : ℤ) ^ k * s * (1 - 2 * t), ?_⟩
      have hq2 : (2 : ℤ) ^ (k + 1) = 4 * (2 : ℤ) ^ (k - 1) := by rw [e1, e4]; ring
      have hq3 : (2 : ℤ) ^ (k + 1 + 1) = 8 * (2 : ℤ) ^ (k - 1) := by
        rw [show k + 1 + 1 = (k + 1) + 1 from rfl, pow_succ', hq2]; ring
      rw [hA1, hB1, hq2, hq3, e4]
      ring

private theorem B_val_one : B 1 = 1 := by decide

private theorem B_val_three : B 3 = 1 := by decide

private theorem A_val_one : A 1 = 1 := by decide

private theorem A_val_three : A 3 = -5 := by decide

/-- Powers of $(1 + \sqrt{-2})^{2^k}$ are $1$ modulo $2^k$. -/
private theorem pow_period_one (k q : ℕ) (hk : 1 ≤ k) :
    ((δ ^ (2 ^ k)) ^ q).re ≡ 1 [ZMOD (2 : ℤ) ^ k] ∧
    ((δ ^ (2 ^ k)) ^ q).im ≡ 0 [ZMOD (2 : ℤ) ^ k] := by
  have hP : (δ ^ (2 ^ k)).re ≡ 1 [ZMOD (2 : ℤ) ^ k] := by
    rcases eq_or_lt_of_le hk with rfl | h2
    · decide
    · exact (pow2k_cong k (by omega)).1.of_dvd (pow_dvd_pow 2 (Nat.le_succ k))
  have hQ : (δ ^ (2 ^ k)).im ≡ 0 [ZMOD (2 : ℤ) ^ k] := by
    rcases eq_or_lt_of_le hk with rfl | h2
    · decide
    · have hB := (pow2k_cong k (by omega)).2.of_dvd (pow_dvd_pow 2 (Nat.le_succ k))
      exact hB.trans (Int.modEq_zero_iff_dvd.mpr (dvd_refl _))
  induction q with
  | zero => simp
  | succ q ih =>
    obtain ⟨ihA, ihB⟩ := ih
    have hre : ((δ ^ (2 ^ k)) ^ (q + 1)).re =
        ((δ ^ (2 ^ k)) ^ q).re * (δ ^ (2 ^ k)).re +
          -2 * ((δ ^ (2 ^ k)) ^ q).im * (δ ^ (2 ^ k)).im := by
      rw [pow_succ, Zsqrtd.re_mul]
    have him : ((δ ^ (2 ^ k)) ^ (q + 1)).im =
        ((δ ^ (2 ^ k)) ^ q).re * (δ ^ (2 ^ k)).im +
          ((δ ^ (2 ^ k)) ^ q).im * (δ ^ (2 ^ k)).re := by
      rw [pow_succ, Zsqrtd.im_mul]
    rw [hre, him]
    constructor
    · calc ((δ ^ (2 ^ k)) ^ q).re * (δ ^ (2 ^ k)).re +
            -2 * ((δ ^ (2 ^ k)) ^ q).im * (δ ^ (2 ^ k)).im
          ≡ 1 * 1 + -2 * 0 * 0 [ZMOD (2 : ℤ) ^ k] :=
            (ihA.mul hP).add ((Int.ModEq.refl (-2)).mul ihB |>.mul hQ)
        _ = 1 := by ring
    · calc ((δ ^ (2 ^ k)) ^ q).re * (δ ^ (2 ^ k)).im +
            ((δ ^ (2 ^ k)) ^ q).im * (δ ^ (2 ^ k)).re
          ≡ 1 * 0 + 0 * 1 [ZMOD (2 : ℤ) ^ k] :=
            (ihA.mul hQ).add (ihB.mul hP)
        _ = 0 := by ring

/-- The imaginary part of $(1 + \sqrt{-2})^n$ depends only on $n$ modulo $2^k$. -/
private theorem B_period (k n : ℕ) (hk : 1 ≤ k) :
    B n ≡ B (n % 2 ^ k) [ZMOD (2 : ℤ) ^ k] := by
  have hper := pow_period_one k (n / 2 ^ k) hk
  have hn : n = 2 ^ k * (n / 2 ^ k) + n % 2 ^ k := (Nat.div_add_mod n (2 ^ k)).symm
  conv_lhs => rw [hn, add_B]
  have hAq : A (2 ^ k * (n / 2 ^ k)) = ((δ ^ (2 ^ k)) ^ (n / 2 ^ k)).re := by
    simp only [A, pow_mul]
  have hBq : B (2 ^ k * (n / 2 ^ k)) = ((δ ^ (2 ^ k)) ^ (n / 2 ^ k)).im := by
    simp only [B, pow_mul]
  rw [hAq, hBq]
  calc ((δ ^ (2 ^ k)) ^ (n / 2 ^ k)).re * B (n % 2 ^ k) +
        ((δ ^ (2 ^ k)) ^ (n / 2 ^ k)).im * A (n % 2 ^ k)
      ≡ 1 * B (n % 2 ^ k) + 0 * A (n % 2 ^ k) [ZMOD (2 : ℤ) ^ k] :=
        (hper.1.mul (Int.ModEq.refl _)).add (hper.2.mul (Int.ModEq.refl _))
    _ = B (n % 2 ^ k) := by ring

/-- If the imaginary part of $(1 + \sqrt{-2})^r$ is $1$ modulo $2^k$, then $r$ is $1$ or $3$. -/
private theorem key (k : ℕ) (hk : 2 ≤ k) : ∀ r : ℕ, r < 2 ^ k →
    B r ≡ 1 [ZMOD (2 : ℤ) ^ k] → r = 1 ∨ r = 3 := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro r hr hB
    have hB0 : B 0 = 0 := by decide
    have hB2 : B 2 = 2 := by decide
    interval_cases r
    · rw [hB0] at hB; exact absurd hB (by decide)
    · exact Or.inl rfl
    · rw [hB2] at hB; exact absurd hB (by decide)
    · exact Or.inr rfl
  | succ k hk ih =>
    intro r hr hB
    set r0 := r % 2 ^ k with hr0def
    set q := r / 2 ^ k with hqdef
    have hr0lt : r0 < 2 ^ k := Nat.mod_lt _ (pow_pos (by norm_num) k)
    have hqle : q < 2 := by
      rw [hqdef, Nat.div_lt_iff_lt_mul (pow_pos (by norm_num) k)]
      have he : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      omega
    have hq : q = 0 ∨ q = 1 := by
      rcases Nat.eq_zero_or_pos q with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hreq : r = 2 ^ k * q + r0 := by
      have h := (Nat.div_add_mod r (2 ^ k)).symm
      rw [← hqdef, ← hr0def] at h
      exact h
    have hB0 : B r0 ≡ 1 [ZMOD (2 : ℤ) ^ k] := by
      have hper := B_period k r (by omega)
      rw [← hr0def] at hper
      have hB' : B r ≡ 1 [ZMOD (2 : ℤ) ^ k] :=
        hB.of_dvd (pow_dvd_pow 2 (Nat.le_succ k))
      exact hper.symm.trans hB'
    rcases ih r0 hr0lt hB0 with h1 | h3
    · rcases hq with hq0 | hq1
      · have hreq' := hreq; rw [hq0, h1] at hreq'
        simp only [mul_zero, zero_add] at hreq'; exact Or.inl hreq'
      · exfalso
        have hBr : B r ≡ 1 + (2 : ℤ) ^ k [ZMOD (2 : ℤ) ^ (k + 1)] := by
          have hr1 : r = 2 ^ k + 1 := by
            have hreq' := hreq; rw [hq1, h1] at hreq'; simpa using hreq'
          rw [hr1, add_B, B_val_one, A_val_one]
          calc A (2 ^ k) * 1 + B (2 ^ k) * 1
              ≡ 1 * 1 + (2 : ℤ) ^ k * 1 [ZMOD (2 : ℤ) ^ (k + 1)] :=
                ((pow2k_cong k hk).1.mul (Int.ModEq.refl _)).add
                  ((pow2k_cong k hk).2.mul (Int.ModEq.refl _))
            _ = 1 + (2 : ℤ) ^ k := by ring
        have hdvd : (2 : ℤ) ^ (k + 1) ∣ (2 : ℤ) ^ k := by
          have h := hBr.symm.trans hB
          rw [Int.modEq_iff_dvd] at h
          have heq : (1 : ℤ) - (1 + (2 : ℤ) ^ k) = -(2 : ℤ) ^ k := by ring
          rw [heq] at h
          exact dvd_neg.mp h
        have hle : (2 : ℤ) ^ (k + 1) ≤ (2 : ℤ) ^ k :=
          Int.le_of_dvd (by positivity) hdvd
        have hlt : (2 : ℤ) ^ k < (2 : ℤ) ^ (k + 1) := by
          rw [pow_succ']; nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) k]
        omega
    · rcases hq with hq0 | hq1
      · have hreq' := hreq; rw [hq0, h3] at hreq'
        simp only [mul_zero, zero_add] at hreq'; exact Or.inr hreq'
      · exfalso
        have hBr : B r ≡ 1 + (2 : ℤ) ^ k [ZMOD (2 : ℤ) ^ (k + 1)] := by
          have hr3 : r = 2 ^ k + 3 := by
            have hreq' := hreq; rw [hq1, h3] at hreq'; simpa using hreq'
          rw [hr3, add_B, B_val_three, A_val_three]
          calc A (2 ^ k) * 1 + B (2 ^ k) * -5
              ≡ 1 * 1 + (2 : ℤ) ^ k * -5 [ZMOD (2 : ℤ) ^ (k + 1)] :=
                ((pow2k_cong k hk).1.mul (Int.ModEq.refl _)).add
                  ((pow2k_cong k hk).2.mul (Int.ModEq.refl _))
            _ ≡ 1 + (2 : ℤ) ^ k [ZMOD (2 : ℤ) ^ (k + 1)] := by
                rw [Int.modEq_iff_dvd]
                refine ⟨3, ?_⟩
                have he : (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k := pow_succ' 2 k
                rw [he]; ring
        have hdvd : (2 : ℤ) ^ (k + 1) ∣ (2 : ℤ) ^ k := by
          have h := hBr.symm.trans hB
          rw [Int.modEq_iff_dvd] at h
          have heq : (1 : ℤ) - (1 + (2 : ℤ) ^ k) = -(2 : ℤ) ^ k := by ring
          rw [heq] at h
          exact dvd_neg.mp h
        have hle : (2 : ℤ) ^ (k + 1) ≤ (2 : ℤ) ^ k :=
          Int.le_of_dvd (by positivity) hdvd
        have hlt : (2 : ℤ) ^ k < (2 : ℤ) ^ (k + 1) := by
          rw [pow_succ']; nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) k]
        omega

/-- The imaginary part of $(1 + \varepsilon\sqrt{-2})^n$ is $\varepsilon$ times that of
$(1 + \sqrt{-2})^n$ when $\varepsilon = \pm 1$. -/
private theorem pow_im_sign (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (n : ℕ) :
    ((⟨1, ε⟩ : ℤ√(-2 : ℤ)) ^ n).im = ε * B n := by
  rcases hε with rfl | rfl
  · change (δ ^ n).im = 1 * B n
    simp only [one_mul, B]
  · have hstar : (⟨1, -1⟩ : ℤ√(-2 : ℤ)) = star δ := rfl
    rw [hstar, ← star_pow]
    simp only [Zsqrtd.im_star, B, neg_one_mul]

private theorem neg_one_pow_or (n : ℕ) : (-1 : ℤ) ^ n = 1 ∨ (-1 : ℤ) ^ n = -1 := by
  rcases Nat.even_or_odd n with h | h
  · exact Or.inl (Even.neg_one_pow h)
  · exact Or.inr (Odd.neg_one_pow h)

/-- The exponent in $3^x = y^2 + 2$ with $x > 0$ is $1$ or $3$. -/
private theorem exponent_eq_one_or_three {x y : ℕ} (h : 3 ^ x = y ^ 2 + 2)
    (hx : 0 < x) : x = 1 ∨ x = 3 := by
  classical
  set α : ℤ√(-2 : ℤ) := ⟨(y : ℤ), 1⟩ with hαdef
  have hnormα : Zsqrtd.norm α = ((3 ^ x : ℕ) : ℤ) := by
    rw [Zsqrtd.norm_def]
    change (y : ℤ) * (y : ℤ) - -2 * 1 * 1 = ((3 ^ x : ℕ) : ℤ)
    rw [h]; push_cast; ring
  have hcop : IsCoprime α (star α) := by
    apply EuclideanDomain.isCoprime_of_dvd
    · intro hcon
      have him := congrArg Zsqrtd.im hcon.1
      simp [hαdef] at him
    · intro z hzmem hz0 hdzα hdzβ
      have hdiff : z ∣ α - star α := dvd_sub hdzα hdzβ
      have hdiff2 : α - star α = (⟨0, 2⟩ : ℤ√(-2 : ℤ)) := by
        apply Zsqrtd.ext <;> simp [hαdef]
      rw [hdiff2] at hdiff
      have h8 := Zsqrtd.natAbs_norm_dvd_of_dvd hdiff
      have h3x := Zsqrtd.natAbs_norm_dvd_of_dvd hdzα
      have hnorm0 : (Zsqrtd.norm (⟨0, 2⟩ : ℤ√(-2 : ℤ))).natAbs = 8 := by decide
      rw [hnorm0] at h8
      have hnorm3 : (Zsqrtd.norm α).natAbs = 3 ^ x := by
        rw [hnormα, Int.natAbs_natCast]
      rw [hnorm3] at h3x
      have hcop8 : Nat.Coprime 8 (3 ^ x) := (by decide : Nat.Coprime 8 3).pow_right x
      have h1 : (Zsqrtd.norm z).natAbs = 1 := by
        have hd := Nat.dvd_gcd h8 h3x
        rw [hcop8.gcd_eq_one] at hd
        exact Nat.dvd_one.mp hd
      exact hzmem (Zsqrtd.norm_eq_one_iff.mp h1)
  have hprod : α * star α = (3 : ℤ√(-2 : ℤ)) ^ x := by
    rw [← Zsqrtd.norm_eq_mul_conj, hnormα]
    norm_cast
  obtain ⟨γ, hγ⟩ := exists_associated_pow_of_mul_eq_pow' hcop hprod
  obtain ⟨u, hu⟩ := hγ
  have hnormγ : Zsqrtd.norm γ = 3 := by
    have h1 := congrArg Zsqrtd.norm hu
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_pow, hnormα] at h1
    have hunorm : Zsqrtd.norm (u : ℤ√(-2 : ℤ)) = 1 := by
      have hnn := Zsqrtd.norm_nonneg (show (-2 : ℤ) ≤ 0 by norm_num) (u : ℤ√(-2 : ℤ))
      have hna := Zsqrtd.norm_eq_one_iff.mpr u.isUnit
      have hna' := Int.natAbs_of_nonneg hnn
      rw [hna] at hna'
      exact hna'.symm
    rw [hunorm, mul_one] at h1
    have hpos : 0 ≤ Zsqrtd.norm γ := Zsqrtd.norm_nonneg (show (-2 : ℤ) ≤ 0 by norm_num) γ
    have hm : (Zsqrtd.norm γ).natAbs = 3 := by
      have h3 : (Zsqrtd.norm γ).natAbs ^ x = 3 ^ x := by
        have hh := congrArg Int.natAbs h1
        rw [Int.natAbs_pow, Int.natAbs_natCast] at hh
        exact hh
      by_contra hne
      rcases lt_trichotomy ((Zsqrtd.norm γ).natAbs) 3 with hlt | heq | hgt
      · exact absurd h3 (ne_of_lt (pow_lt_pow_left₀ hlt (Nat.zero_le _) hx.ne'))
      · exact hne heq
      · exact absurd h3.symm (ne_of_lt (pow_lt_pow_left₀ hgt (Nat.zero_le _) hx.ne'))
    have hna' := Int.natAbs_of_nonneg hpos
    rw [hm] at hna'
    exact hna'.symm
  obtain ⟨a, b⟩ := γ
  have hnormab : a ^ 2 + 2 * b ^ 2 = 3 := by
    have hh := hnormγ
    rw [Zsqrtd.norm_def] at hh
    change a * a - -2 * b * b = 3 at hh
    linear_combination hh
  have hsq : ∀ z : ℤ, z ^ 2 ≠ 3 := by
    intro z hz
    have h4 := congrArg (fun w : ℤ => (w : ZMod 4)) hz
    push_cast at h4
    exact (by decide : ∀ w : ZMod 4, w ^ 2 ≠ 3) _ h4
  have hb2 : b ^ 2 = 1 := by
    have hb_le : b ^ 2 ≤ 1 := by
      by_contra hc
      have h2 : 2 ≤ b ^ 2 := by have hlt := not_le.mp hc; omega
      linarith [sq_nonneg a, hnormab, h2]
    have hb_ne : b ^ 2 ≠ 0 := by
      intro h0
      have ha3 : a ^ 2 = 3 := by omega
      exact hsq a ha3
    have hnn : 0 ≤ b ^ 2 := sq_nonneg b
    omega
  have ha2 : a ^ 2 = 1 := by omega
  have ha : a = 1 ∨ a = -1 := sq_eq_one_iff.mp ha2
  have hb : b = 1 ∨ b = -1 := sq_eq_one_iff.mp hb2
  have hε : a * b = 1 ∨ a * b = -1 := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  have hγeq : (⟨a, b⟩ : ℤ√(-2 : ℤ)) = ((a : ℤ) : ℤ√(-2 : ℤ)) * ⟨1, a * b⟩ := by
    apply Zsqrtd.ext
    · simp
    · simp [show a * (a * b) = b by
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> ring]
  have himγ : ((⟨a, b⟩ : ℤ√(-2 : ℤ)) ^ x).im = a ^ x * (a * b) * B x := by
    have hcast : (((a : ℤ) : ℤ√(-2 : ℤ)) ^ x) = ((a ^ x : ℤ) : ℤ√(-2 : ℤ)) := by
      push_cast; ring
    rw [hγeq, mul_pow, Zsqrtd.im_mul, pow_im_sign _ hε, hcast]
    simp only [Zsqrtd.re_intCast, Zsqrtd.im_intCast, zero_mul, add_zero]
    ring
  have himα : (1 : ℤ) = ((⟨a, b⟩ : ℤ√(-2 : ℤ)) ^ x).re * (u : ℤ√(-2 : ℤ)).im +
      ((⟨a, b⟩ : ℤ√(-2 : ℤ)) ^ x).im * (u : ℤ√(-2 : ℤ)).re := by
    have hαim : α.im = 1 := by simp [hαdef]
    rw [← hαim, ← hu, Zsqrtd.im_mul]
  have huval : (u : ℤ√(-2 : ℤ)) = 1 ∨ (u : ℤ√(-2 : ℤ)) = -1 :=
    Zsqrtd.NegTwo.zsqrtd_neg_two_isUnit_iff _ |>.mp u.isUnit
  have hBpm : B x = 1 ∨ B x = -1 := by
    have hax : a ^ x = 1 ∨ a ^ x = -1 := by
      rcases ha with rfl | rfl
      · simp
      · exact neg_one_pow_or x
    rcases huval with hu1 | hu1 <;> rcases hax with hax1 | hax1 <;>
      rcases hε with hε1 | hε1 <;>
      (rw [hu1] at himα;
       simp only [Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_neg, Zsqrtd.im_neg,
         mul_zero, mul_one, mul_neg, neg_zero] at himα;
       rw [himγ, hax1, hε1] at himα; omega)
  rcases hBpm with hB1 | hB1
  · have hk : x < 2 ^ (x + 2) := by
      calc x < 2 ^ x := Nat.lt_two_pow_self
        _ ≤ 2 ^ (x + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact key (x + 2) (by omega) x hk (by rw [hB1])
  · exfalso
    have hper2 : B x ≡ B (x % 8) [ZMOD (8 : ℤ)] := B_period 3 x (by norm_num)
    rw [hB1] at hper2
    have hmod : B (x % 8) ≡ (-1 : ℤ) [ZMOD 8] := hper2.symm
    have hlt : x % 8 < 8 := Nat.mod_lt _ (by norm_num)
    rcases (show x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨
        x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 by omega) with h | h | h | h | h | h | h | h <;>
      rw [h] at hmod <;> exact absurd hmod (by decide)

end three_pow_eq_sq_add_two_iff

open three_pow_eq_sq_add_two_iff

/-- **Solutions of $3^x = y^2 + 2$.** For natural numbers $x, y$, we have $3^x = y^2 + 2$ if and
only if $(x, y)$ is $(1, 1)$ or $(3, 5)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 8. -/
public theorem three_pow_eq_sq_add_two_iff (x y : ℕ) :
    3 ^ x = y ^ 2 + 2 ↔ (x, y) = (1, 1) ∨ (x, y) = (3, 5) := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · omega
    · rcases exponent_eq_one_or_three h hx with rfl | rfl
      · have hy2 : y ^ 2 = 1 := by omega
        have hy : y = 1 := by
          have hZ : (y : ℤ) ^ 2 = (1 : ℤ) ^ 2 := by exact_mod_cast hy2
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hZ with h' | h' <;> omega
        subst hy
        exact Or.inl rfl
      · have hy2 : y ^ 2 = 25 := by omega
        have hy : y = 5 := by
          have hZ : (y : ℤ) ^ 2 = (5 : ℤ) ^ 2 := by exact_mod_cast hy2
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hZ with h' | h' <;> omega
        subst hy
        exact Or.inr rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

end MetaMathlibExt
