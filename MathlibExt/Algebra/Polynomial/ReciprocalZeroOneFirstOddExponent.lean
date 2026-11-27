/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import MathlibExt.Algebra.Polynomial.ZeroOneSquareComposition
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The first odd exponent of a reciprocal `0,1`-polynomial

This file defines reciprocal and non-cyclotomic integer polynomials and proves
`l_eq_min_support_and_lt`, from Pradipto Banerjee and Amit Kundu, "On an Irreducibility
Question Concerning Palindromic Non-cyclotomic 0,1-Polynomials", *INTEGERS* 24 (2024),
Article A71 (<https://math.colgate.edu/~integers/vol24.html>): let `f` be an irreducible,
reciprocal, non-cyclotomic `0,1`-polynomial of degree `2 * m` such that `f(x^2)` is
reducible, and write `f(x) = f_e(x^2) + x^l f_o(x^2)` with `l` odd and positive,
`deg f_e = m` and `deg f_o = m - l`. Then `x^l` is the first monomial of `f` after the
constant term, and `2 * l < m`.

The proof compares coefficients in the congruence `f(x^2) ≡ f(x) f(-x) (mod 4)` of
`map_comp_sq_eq_mul`. Comparing the coefficients of `x^(2t)` shows that the first positive
exponent of `f` is odd. Since `f` is reciprocal, the leading coefficient of `f_o` then forces
`m ≥ l` and places that exponent at `l`. Next, the coefficient of `x^(2l)` is `1` and the
positive even exponents below `2l` are absent; with the symmetry of `f`, this leaves `m = l` or
`m ≥ 2l`. In the boundary case `m = l`, the symmetry of `f` gives
`f = 1 + x^l + x^(2l)`; in the boundary case `m = 2l`, one more comparison of coefficients
gives `f = 1 + x^l + x^(2l) + x^(3l) + x^(4l)`. These divide `x^(3l) - 1` and `x^(5l) - 1`,
so being irreducible `f` would be a cyclotomic polynomial, which the hypotheses exclude.

The predicates `IsReciprocalPoly` and `IsNoncyclotomic` and their characterizations
moved here from the wanted module `WantedExt.Algebra.PalindromicZeroOneWanted` when this
statement was proved, with the same names and statements.
-/

set_option autoImplicit false

@[expose] public section

open Polynomial Finset

namespace MathlibExt.Algebra.PalindromicZeroOneWanted

/-- **Reciprocal polynomial.** A polynomial $f(x) = a_0 + a_1 x + \dots + a_d x^d$ in
$\mathbb{Z}[x]$ of degree $d$ (with $d = 0$ for the zero polynomial) is *reciprocal*
(palindromic) if it equals its reversal $x^d f(1/x)$, that is, if $a_i = a_{d-i}$ for all
$0 \le i \le d$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
def IsReciprocalPoly (f : ℤ[X]) : Prop :=
  f.reverse = f

/-- **Characterization of reciprocal polynomials.** A polynomial $f \in \mathbb{Z}[x]$ of
degree $d$ (with $d = 0$ for the zero polynomial) is reciprocal if and only if its reversal
$x^d f(1/x)$ equals $f$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
theorem isReciprocalPoly_iff (f : ℤ[X]) :
    IsReciprocalPoly f ↔ f.reverse = f :=
  Iff.rfl

/-- **Non-cyclotomic polynomial.** A polynomial $f \in \mathbb{Z}[x]$ is *non-cyclotomic* if
$f \ne \Phi_n$ for every positive integer $n$, where $\Phi_n$ denotes the $n$-th cyclotomic
polynomial.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
def IsNoncyclotomic (f : ℤ[X]) : Prop :=
  ∀ n : ℕ, 0 < n → f ≠ Polynomial.cyclotomic n ℤ

/-- **Characterization of non-cyclotomic polynomials.** A polynomial $f \in \mathbb{Z}[x]$ is
non-cyclotomic if and only if $f \ne \Phi_n$ for every positive integer $n$, where $\Phi_n$
denotes the $n$-th cyclotomic polynomial.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
theorem isNoncyclotomic_iff (f : ℤ[X]) :
    IsNoncyclotomic f ↔
      ∀ n : ℕ, 0 < n → f ≠ Polynomial.cyclotomic n ℤ :=
  Iff.rfl

/-- An irreducible monic integer polynomial dividing `X ^ n - 1` is cyclotomic. -/
private theorem exists_eq_cyclotomic_of_dvd {f : ℤ[X]} {n : ℕ} (hn : 0 < n)
    (hirr : Irreducible f) (hmonic : f.Monic) (hdvd : f ∣ X ^ n - 1) :
    ∃ d, 0 < d ∧ f = cyclotomic d ℤ := by
  rw [← prod_cyclotomic_eq_X_pow_sub_one hn] at hdvd
  obtain ⟨d, hd, hfd⟩ := (hirr.prime.dvd_finsetProd_iff _).mp hdvd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  exact ⟨d, hd0, eq_of_monic_of_associated hmonic (cyclotomic.monic d ℤ)
    (hirr.associated_of_dvd (cyclotomic.irreducible hd0) hfd)⟩

/-- An antidiagonal sum whose terms vanish outside three positions. -/
private theorem sum_antidiagonal_eq {R : Type*} [CommRing R] (a : ℕ → R) {t b : ℕ}
    (hb : b < t)
    (h : ∀ i j, i + j = 2 * t → i ≠ b → i ≠ 2 * t - b → i ≠ t → a i * a j = 0) :
    ∑ x ∈ antidiagonal (2 * t), a x.1 * (a x.2 * (-1) ^ x.2) =
      2 * (-1) ^ b * a b * a (2 * t - b) + (-1) ^ t * a t * a t := by
  have hsub : ({(b, 2 * t - b), (2 * t - b, b), (t, t)} : Finset (ℕ × ℕ)) ⊆
      antidiagonal (2 * t) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_antidiagonal]
    rcases hx with rfl | rfl | rfl <;> dsimp only <;> omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_insert, Finset.sum_pair]
    · have hpow : (-1 : R) ^ (2 * t - b) = (-1) ^ b := by
        rw [show 2 * t - b = b + 2 * (t - b) by omega, pow_add, pow_mul, neg_one_sq, one_pow,
          mul_one]
      dsimp only
      rw [hpow]
      ring
    · simp only [ne_eq, Prod.mk.injEq, not_and]
      omega
    · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
      omega
  · rintro ⟨i, j⟩ hx hx'
    rw [mem_antidiagonal] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or] at hx'
    rw [← mul_assoc, h i j hx (by omega) (by omega) (by omega), zero_mul]

/-- Coefficientwise form of `f(x²) ≡ f(x) f(-x) (mod 4)`. -/
private theorem coeff_rel {f : ℤ[X]}
    (h : (f.comp (X ^ 2)).map (Int.castRingHom (ZMod 4)) =
      (f * f.comp (-X)).map (Int.castRingHom (ZMod 4))) (t : ℕ) :
    (f.coeff t : ZMod 4) = ∑ x ∈ antidiagonal (2 * t),
      (f.coeff x.1 : ZMod 4) * ((f.coeff x.2 : ZMod 4) * (-1) ^ x.2) := by
  have := congrArg (fun p : (ZMod 4)[X] => p.coeff (2 * t)) h
  simp only [coeff_map, coeff_mul, ← expand_eq_comp_X_pow, coeff_expand_mul' two_pos,
    map_sum, map_mul, eq_intCast] at this
  rw [this]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show (-X : ℤ[X]) = C (-1) * X by simp, comp_C_mul_X_coeff]
  push_cast
  rfl

section Stages

variable {a : ℕ → ZMod 4}
  (hrel : ∀ t, a t = ∑ x ∈ antidiagonal (2 * t), a x.1 * (a x.2 * (-1) ^ x.2))
include hrel

/-- The first positive exponent is odd. -/
private theorem odd_of_first (h0 : a 0 = 1) {s : ℕ} (hs0 : 0 < s) (hs : a s = 1)
    (hmin : ∀ i, 0 < i → i < s → a i = 0) : Odd s := by
  rcases Nat.even_or_odd s with ⟨t, ht⟩ | h
  · exfalso
    have ht0 : 0 < t := by omega
    have key := hrel t
    rw [sum_antidiagonal_eq a (b := 0) ht0 fun i j hij hi1 hi2 hi3 => by
      rw [hmin i (by omega) (by omega), zero_mul]] at key
    rw [hmin t ht0 (by omega), h0, Nat.sub_zero, show 2 * t = s by omega, hs] at key
    simp only [pow_zero, mul_one, mul_zero, add_zero] at key
    exact absurd key (by decide)
  · exact h

/-- The positive even exponents strictly below `2 * l` are absent, and `2 * l` is present. -/
private theorem even_coeffs (ha : ∀ i, a i = 0 ∨ a i = 1) (h0 : a 0 = 1) {l : ℕ} (hl : Odd l)
    (hlow : ∀ i, 0 < i → i < l → a i = 0) (hal : a l = 1) :
    (∀ t, 0 < t → t < l → a (2 * t) = 0) ∧ a (2 * l) = 1 := by
  have hl0 : 0 < l := hl.pos
  have hvan : ∀ t, t ≤ l → ∀ i j, i + j = 2 * t → i ≠ 0 → i ≠ 2 * t - 0 → i ≠ t →
      a i * a j = 0 := by
    intro t htl i j hij hi1 hi2 hi3
    rcases lt_or_ge i l with hil | hil
    · rw [hlow i (by omega) hil, zero_mul]
    · rw [hlow j (by omega) (by omega), mul_zero]
  constructor
  · intro t ht0 htl
    have key := hrel t
    rw [sum_antidiagonal_eq a (b := 0) ht0 (hvan t htl.le), hlow t ht0 htl, h0,
      Nat.sub_zero] at key
    rcases ha (2 * t) with h | h
    · exact h
    · rw [h] at key
      simp only [pow_zero, mul_one, mul_zero, add_zero] at key
      exact absurd key (by decide)
  · have key := hrel l
    rw [sum_antidiagonal_eq a (b := 0) hl0 (hvan l le_rfl), hal, h0, Nat.sub_zero,
      hl.neg_one_pow] at key
    rcases ha (2 * l) with h | h
    · rw [h] at key
      simp only [pow_zero, mul_one, mul_zero, zero_add] at key
      exact absurd key (by decide)
    · exact h

/-- An odd exponent strictly between `l` and `2 * l` cannot come first after `l`. -/
private theorem false_of_mid {l s : ℕ} (hl : Odd l) (hs : Odd s) (hls : l < s)
    (hlow : ∀ i, 0 < i → i < l → a i = 0) (hal : a l = 1) (has : a s = 1)
    (hmid : ∀ i, l < i → i < s → a i = 0) (hsum : a (l + s) = 0) : False := by
  obtain ⟨k, rfl⟩ := hl
  obtain ⟨k', rfl⟩ := hs
  have key := hrel (k + k' + 1)
  rw [sum_antidiagonal_eq a (b := 2 * k + 1) (t := k + k' + 1) (by omega) ?_] at key
  · rw [hmid (k + k' + 1) (by omega) (by omega), hal,
      show 2 * (k + k' + 1) - (2 * k + 1) = 2 * k' + 1 by omega, has,
      (odd_two_mul_add_one k).neg_one_pow] at key
    simp only [mul_one, mul_zero, add_zero] at key
    exact absurd key (by decide)
  · intro i j hij hi1 hi2 hi3
    rcases Nat.lt_or_ge i (2 * k + 1) with h1 | h1
    · rcases Nat.eq_zero_or_pos i with rfl | h2
      · rw [show j = 2 * k + 1 + (2 * k' + 1) by omega, hsum, mul_zero]
      · rw [hlow i h2 h1, zero_mul]
    · rcases Nat.lt_or_ge i (2 * k' + 1) with h3 | h3
      · rw [hmid i (by omega) h3, zero_mul]
      · rcases Nat.eq_zero_or_pos j with rfl | h4
        · rw [show i = 2 * k + 1 + (2 * k' + 1) by omega, hsum, zero_mul]
        · rw [hlow j h4 (by omega), mul_zero]

end Stages

/-- **Position of the first odd exponent.** Let $f \in \mathbb{Z}[x]$ be an irreducible,
reciprocal, non-cyclotomic $0,1$-polynomial of degree $2m$ such that $f(x^2)$ is not
irreducible. Let $f_e, f_o \in \mathbb{Z}[x]$ and let $\ell$ be a positive odd integer with
$f(x) = f_e(x^2) + x^\ell f_o(x^2)$, $\deg f_e = m$ and $\deg f_o = \max(m - \ell, 0)$, where
the degree of the zero polynomial is taken to be $0$. Then the coefficient of $x^e$ in $f$ is
$0$ for every $1 \le e < \ell$, the coefficient of $x^\ell$ in $f$ is nonzero, and $2\ell < m$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", INTEGERS 24 (2024),
Article A71, Lemma 3. -/
theorem l_eq_min_support_and_lt (f fe fo : ℤ[X]) (m l : ℕ)
    (h01 : IsZeroOnePoly f) (hirr : Irreducible f)
    (hrec : IsReciprocalPoly f) (hnc : IsNoncyclotomic f)
    (hdeg : f.natDegree = 2 * m)
    (hdecomp : f = fe.comp (X ^ 2) + X ^ l * fo.comp (X ^ 2))
    (hfe : fe.natDegree = m) (hfo : fo.natDegree = m - l)
    (hl : Odd l) (hl0 : 0 < l)
    (hred : ¬ Irreducible (f.comp (X ^ 2))) :
    (∀ e : ℕ, 1 ≤ e → e < l → f.coeff e = 0) ∧
      f.coeff l ≠ 0 ∧ 2 * l < m := by
  classical
  -- Basic facts: `f` is monic, palindromic of degree `2 * m`, with constant term `1`.
  have hlc : f.leadingCoeff = 1 := (h01 _).resolve_left (leadingCoeff_ne_zero.mpr hirr.ne_zero)
  have hf0 : f.coeff 0 = 1 := by
    unfold IsReciprocalPoly at hrec
    rw [← hrec, coeff_zero_reverse, hlc]
  have hsymm : ∀ i ≤ 2 * m, f.coeff (2 * m - i) = f.coeff i := by
    intro i hi
    conv_rhs => rw [← show f.reverse = f from hrec]
    rw [coeff_reverse, hdeg, revAt_le hi]
  have hbig : ∀ i, 2 * m < i → f.coeff i = 0 := fun i hi =>
    coeff_eq_zero_of_natDegree_lt (hdeg ▸ hi)
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · refine absurd ?_ hirr.not_isUnit
      rw [eq_C_of_natDegree_eq_zero (by omega : f.natDegree = 0), hf0, C_1]
      exact isUnit_one
    · exact h
  have hc2m : f.coeff (2 * m) = 1 := by simpa [hf0] using hsymm 0 (Nat.zero_le _)
  -- The odd part of `f` is `X ^ l * fo(X ^ 2)`.
  have hcoeff : ∀ i, f.coeff i = (if 2 ∣ i then fe.coeff (i / 2) else 0) +
      (if l ≤ i then (if 2 ∣ i - l then fo.coeff ((i - l) / 2) else 0) else 0) := by
    intro i
    rw [hdecomp, coeff_add, coeff_X_pow_mul', ← expand_eq_comp_X_pow, ← expand_eq_comp_X_pow,
      coeff_expand two_pos, coeff_expand two_pos]
  have hodd_lt : ∀ i, Odd i → i < l → f.coeff i = 0 := by
    rintro i ⟨k, rfl⟩ hi
    rw [hcoeff, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
  have hodd_ge : ∀ i, Odd i → l ≤ i → f.coeff i = fo.coeff ((i - l) / 2) := by
    rintro i ⟨k, rfl⟩ hi
    obtain ⟨j, rfl⟩ := hl
    rw [hcoeff, ite_eq_right (by omega), ite_eq_left hi, ite_eq_left (by omega), zero_add]
  -- The coefficients modulo `4`.
  set a : ℕ → ZMod 4 := fun i => (f.coeff i : ZMod 4) with ha_def
  have hza : ∀ i, a i = 0 ↔ f.coeff i = 0 := by
    intro i
    rcases h01 i with h | h
    · simp [ha_def, h]
    · simp only [ha_def, h, Int.cast_one, one_ne_zero, iff_false]
      decide
  have hoa : ∀ i, f.coeff i ≠ 0 → a i = 1 := by
    intro i hi
    rcases h01 i with h | h
    · exact absurd h hi
    · simp [ha_def, h]
  have ha01 : ∀ i, a i = 0 ∨ a i = 1 := by
    intro i
    rcases h01 i with h | h <;> simp [ha_def, h]
  have ha0 : a 0 = 1 := by simp [ha_def, hf0]
  have hrel : ∀ t, a t = ∑ x ∈ antidiagonal (2 * t), a x.1 * (a x.2 * (-1) ^ x.2) :=
    coeff_rel (map_comp_sq_eq_mul f h01 hirr hf0 hred)
  -- The first positive exponent of `f` is odd.
  have hex : ∃ i, 0 < i ∧ f.coeff i ≠ 0 := ⟨2 * m, by omega, by rw [hc2m]; exact one_ne_zero⟩
  obtain ⟨hs0, hs⟩ := Nat.find_spec hex
  have hmin : ∀ i, 0 < i → i < Nat.find hex → f.coeff i = 0 := fun i hi his => by
    have := Nat.find_min hex his
    push Not at this
    exact this hi
  have hs_odd : Odd (Nat.find hex) := odd_of_first hrel ha0 hs0 (hoa _ hs)
    fun i hi his => (hza i).mpr (hmin i hi his)
  -- It is at least `l`, and `fo ≠ 0`.
  have hls : l ≤ Nat.find hex := by
    by_contra h
    exact hs (hodd_lt _ hs_odd (by omega))
  have hfo0 : fo ≠ 0 := by
    intro h0
    apply hs
    rw [hodd_ge _ hs_odd hls, h0, coeff_zero]
  -- By symmetry, the leading coefficient of `fo` gives `m ≥ l` and `f.coeff l ≠ 0`.
  have hlead : f.coeff (l + 2 * fo.natDegree) ≠ 0 := by
    obtain ⟨j, hj⟩ := hl
    rw [hodd_ge _ ⟨j + fo.natDegree, by omega⟩ (by omega),
      show (l + 2 * fo.natDegree - l) / 2 = fo.natDegree by omega]
    exact leadingCoeff_ne_zero.mpr hfo0
  have hle : l + 2 * fo.natDegree ≤ 2 * m := by
    by_contra h
    exact hlead (hbig _ (by omega))
  have hrefl : f.coeff (2 * m - (l + 2 * fo.natDegree)) ≠ 0 := by rwa [hsymm _ hle]
  have hge : l ≤ 2 * m - (l + 2 * fo.natDegree) := by
    by_contra h
    obtain ⟨j, hj⟩ := hl
    exact hrefl (hodd_lt _ ⟨m - j - fo.natDegree - 1, by omega⟩ (by omega))
  have hml : l ≤ m := by
    by_contra h
    rw [hfo] at hge
    omega
  rw [hfo, show 2 * m - (l + 2 * (m - l)) = l by omega] at hrefl
  have hsl : Nat.find hex = l := le_antisymm (Nat.find_min' hex ⟨hl0, hrefl⟩) hls
  have hlow : ∀ e, 0 < e → e < l → f.coeff e = 0 := fun e he hel => hmin e he (hsl ▸ hel)
  refine ⟨hlow, hrefl, ?_⟩
  -- The even exponents below `2 * l` and the exponent `2 * l`.
  have hlow' : ∀ i, 0 < i → i < l → a i = 0 := fun i hi hil => (hza i).mpr (hlow i hi hil)
  have hal : a l = 1 := hoa l hrefl
  obtain ⟨hev, h2l⟩ := even_coeffs hrel ha01 ha0 hl hlow' hal
  have hev' : ∀ t, 0 < t → t < l → f.coeff (2 * t) = 0 := fun t ht htl =>
    (hza _).mp (hev t ht htl)
  have hc2l : f.coeff (2 * l) = 1 := by
    rcases h01 (2 * l) with h | h
    · rw [(hza _).mpr h] at h2l
      exact absurd h2l (by decide)
    · exact h
  have hcl : f.coeff l = 1 := (h01 l).resolve_left hrefl
  have hmonic : f.Monic := hlc
  -- So `m = l` or `2 * l ≤ m`.
  have hcase : m = l ∨ 2 * l ≤ m := by
    rcases eq_or_lt_of_le hml with h | h
    · exact Or.inl h.symm
    · refine Or.inr (by_contra fun hlt => ?_)
      have := hev' (m - l) (by omega) (by omega)
      rw [show 2 * (m - l) = 2 * m - 2 * l by omega, hsymm _ (by omega), hc2l] at this
      exact one_ne_zero this
  rcases hcase with h | h
  · -- `m = l`: then `f = 1 + X ^ l + X ^ (2 * l)` divides `X ^ (3 * l) - 1`.
    exfalso
    subst h
    have hf : f = 1 + X ^ m + X ^ (2 * m) := by
      ext n
      simp only [coeff_add, coeff_one, coeff_X_pow]
      rcases (show n = 0 ∨ (0 < n ∧ n < m) ∨ n = m ∨ (m < n ∧ n < 2 * m) ∨ n = 2 * m ∨
          2 * m < n by omega) with h | h | h | h | h | h
      · rw [h, hf0]; split_ifs <;> omega
      · rw [hlow n h.1 h.2]; split_ifs <;> omega
      · rw [h, hcl]; split_ifs <;> omega
      · rw [← hsymm n (by omega), hlow _ (by omega) (by omega)]; split_ifs <;> omega
      · rw [h, hc2m]; split_ifs <;> omega
      · rw [hbig n h]; split_ifs <;> omega
    obtain ⟨d, hd, hfd⟩ := exists_eq_cyclotomic_of_dvd (n := 3 * m) (by omega) hirr hmonic
      ⟨X ^ m - 1, by rw [hf]; ring⟩
    exact hnc d hd hfd
  rcases eq_or_lt_of_le h with h | h
  · -- `m = 2 * l`: the odd exponents strictly between `l` and `3 * l` vanish.
    exfalso
    subst h
    have hsum : ∀ n, Even n → 2 * l < n → n < 4 * l → f.coeff n = 0 := by
      rintro n ⟨t, rfl⟩ h1 h2
      rw [← hsymm _ (by omega), show 2 * (2 * l) - (t + t) = 2 * (2 * l - t) by omega]
      exact hev' _ (by omega) (by omega)
    have hmid : ∀ n, l < n → n < 2 * l → f.coeff n = 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2, h3⟩ := Nat.find_spec hcon
      have hmin2 : ∀ i, l < i → i < Nat.find hcon → f.coeff i = 0 := fun i hi his => by
        have := Nat.find_min hcon his
        push Not at this
        exact this hi (by omega)
      have hodd2 : Odd (Nat.find hcon) := by
        rcases Nat.even_or_odd (Nat.find hcon) with ⟨t, ht⟩ | h
        · exact absurd (by rw [ht, ← two_mul]; exact hev' t (by omega) (by omega)) h3
        · exact h
      refine false_of_mid hrel hl hodd2 h1 hlow' hal (hoa _ h3)
        (fun i hi his => (hza i).mpr (hmin2 i hi his)) ((hza _).mpr ?_)
      obtain ⟨j, hj⟩ := hl
      obtain ⟨k, hk⟩ := hodd2
      exact hsum _ ⟨j + k + 1, by omega⟩ (by omega) (by omega)
    have hf : f = 1 + X ^ l + X ^ (2 * l) + X ^ (3 * l) + X ^ (4 * l) := by
      ext n
      simp only [coeff_add, coeff_one, coeff_X_pow]
      rcases (show n = 0 ∨ (0 < n ∧ n < l) ∨ n = l ∨ (l < n ∧ n < 2 * l) ∨ n = 2 * l ∨
          (2 * l < n ∧ n < 3 * l) ∨ n = 3 * l ∨ (3 * l < n ∧ n < 4 * l) ∨ n = 4 * l ∨
          4 * l < n by omega) with h | h | h | h | h | h | h | h | h | h
      · rw [h, hf0]; split_ifs <;> omega
      · rw [hlow n h.1 h.2]; split_ifs <;> omega
      · rw [h, hcl]; split_ifs <;> omega
      · rw [hmid n h.1 h.2]; split_ifs <;> omega
      · rw [h, hc2l]; split_ifs <;> omega
      · rw [← hsymm n (by omega), hmid _ (by omega) (by omega)]; split_ifs <;> omega
      · rw [h, ← hsymm _ (by omega), show 2 * (2 * l) - 3 * l = l by omega, hcl]
        split_ifs <;> omega
      · rw [← hsymm n (by omega), hlow _ (by omega) (by omega)]; split_ifs <;> omega
      · rw [h, show 4 * l = 2 * (2 * l) by ring, hc2m]; split_ifs <;> omega
      · rw [hbig n (by omega)]; split_ifs <;> omega
    obtain ⟨d, hd, hfd⟩ := exists_eq_cyclotomic_of_dvd (n := 5 * l) (by omega) hirr hmonic
      ⟨X ^ l - 1, by rw [hf]; ring⟩
    exact hnc d hd hfd
  · exact h

end MathlibExt.Algebra.PalindromicZeroOneWanted
