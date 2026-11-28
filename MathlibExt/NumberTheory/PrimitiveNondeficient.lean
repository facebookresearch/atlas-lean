/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.Factorization.Basic
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
import MathlibExt.NumberTheory.ArithmeticFunction.AbundancyIndexDiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Rat.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dichotomy for odd primitive non-deficient numbers

This file proves the dichotomy for odd primitive non-deficient numbers: for such a number
with least and greatest prime factors `p₁` and `p_k` and radical `R`, either `p_k < √R`
or some prime power component `p ^ (a + 1)` is below `(k + 2 + p₁) * (p_k - 1)`. The
argument tracks the excess of the radical over twice the phi-product modulo the largest
prime factor, then applies a Puchta-style abundancy estimate.

Statements from Joshua Zelinsky, "Must a Primitive Non-Deficient
Number Always Have a Small Component?", *Journal of Integer
Sequences* 29 (2026), Article 26.4.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Zelinsky/zel14.tex>).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PrimitiveNondeficientWanted

/-- Every prime factor of an odd number is odd. -/
private theorem odd_of_mem_primeFactors (n q : ℕ) (hno : Odd n)
    (hq : q ∈ n.primeFactors) : Odd q := by
  rcases Nat.even_or_odd q with hev | hodd
  · exfalso
    have h2 : 2 ∣ n :=
      dvd_trans (even_iff_two_dvd.mp hev) (Nat.dvd_of_mem_primeFactors hq)
    exact (Nat.not_even_iff_odd.mpr hno) (even_iff_two_dvd.mpr h2)
  · exact hodd

/-- Every prime factor of an odd number is at least three. -/
private theorem three_le_of_mem_primeFactors (n q : ℕ) (hno : Odd n)
    (hq : q ∈ n.primeFactors) : 3 ≤ q := by
  have hprime : q.Prime := (Nat.mem_primeFactors.mp hq).1
  obtain ⟨m, hm⟩ := odd_of_mem_primeFactors n q hno hq
  have h2 := hprime.two_le
  omega

/-- The abundancy index of a positive number is positive. -/
private theorem abundancyIndex_pos (m : ℕ) (hm : 0 < m) :
    0 < abundancyIndex m := by
  rw [abundancyIndex]
  apply div_pos _ (by exact_mod_cast hm)
  have hle : m ≤ ∑ d ∈ Nat.divisors m, d :=
    Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
      (Nat.mem_divisors_self m hm.ne')
  have hleQ : (m : ℚ) ≤ ((∑ d ∈ Nat.divisors m, d : ℕ) : ℚ) := by exact_mod_cast hle
  have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  linarith [hleQ]

/-- Abundancy as the supremum bound times correction factors. -/
private theorem abundancyIndex_eq_sup_mul (n : ℕ) (hn0 : n ≠ 0) :
    abundancyIndex n = abundancySup n *
      ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ (n.factorization p + 1)) := by
  have hcop : ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, p ≠ q →
      (p ^ n.factorization p).Coprime (q ^ n.factorization q) := by
    intro p hp q hq hpq
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hqq : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact ((Nat.coprime_primes hpp hqq).mpr hpq).pow_left _ |>.pow_right _
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
  rw [abundancyIndex_prod _ _ hcop]
  simp only [abundancySup, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact abundancyIndex_prime_pow_eq p _ ((Nat.mem_primeFactors.mp hp).1)

/-- Product of `p/(p-1)` over distinct naturals, bounded by telescoping. -/
private theorem prod_div_sub_one_le (T : Finset ℕ) (c : ℕ) (hc : 1 ≤ c)
    (hT : ∀ p ∈ T, c + 1 ≤ p) :
    (∏ p ∈ T, ((p : ℚ) / ((p : ℚ) - 1))) ≤ ((c + T.card : ℕ) : ℚ) / (c : ℚ) := by
  classical
  suffices h : ∀ U : Finset ℕ, (∀ p ∈ U, c + 1 ≤ p) →
      (∏ p ∈ U, ((p : ℚ) / ((p : ℚ) - 1))) ≤ ((c + U.card : ℕ) : ℚ) / (c : ℚ)
    from h T hT
  intro U
  refine Finset.induction_on_max U ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.card_empty]
    simp only [add_zero]
    have hcQ0 : (c : ℚ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
    rw [div_self hcQ0]
  · intro a s hall IH hU
    have hsT : ∀ p ∈ s, c + 1 ≤ p := fun p hp => hU p (Finset.mem_insert_of_mem hp)
    have hIH := IH hsT
    have ha_le : c + 1 ≤ a := hU a (Finset.mem_insert_self a s)
    have ha_notin : a ∉ s := by
      intro hm; exact absurd (hall a hm) (lt_irrefl a)
    have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha_notin
    have hsub : s ⊆ Finset.Ico (c + 1) a := by
      intro x hx
      simp only [Finset.mem_Ico]
      exact ⟨hsT x hx, hall x hx⟩
    have hcle : s.card ≤ a - (c + 1) := by
      calc s.card ≤ (Finset.Ico (c + 1) a).card := Finset.card_le_card hsub
        _ = a - (c + 1) := Nat.card_Ico _ _
    have hmj : c + s.card + 1 ≤ a := by omega
    have hcardQm : c + (s.card + 1) = c + s.card + 1 := by omega
    rw [Finset.prod_insert ha_notin, hcard, hcardQm]
    have hcQ : (0 : ℚ) < (c : ℚ) := by exact_mod_cast (by omega : 0 < c)
    have hjQ : (0 : ℚ) ≤ (s.card : ℚ) := Nat.cast_nonneg _
    have haQ2 : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast (by omega : 2 ≤ a)
    have hcc2 : ((c + s.card : ℕ) : ℚ) = (c : ℚ) + (s.card : ℚ) := by push_cast; ring
    have hBp : ((c + s.card + 1 : ℕ) : ℚ) = ((c + s.card : ℕ) : ℚ) + 1 := by push_cast; ring
    have hmjQ : ((c + s.card + 1 : ℕ) : ℚ) ≤ (a : ℚ) := by exact_mod_cast hmj
    have hmono : (a : ℚ) / ((a : ℚ) - 1)
        ≤ ((c + s.card + 1 : ℕ) : ℚ) / ((c + s.card : ℕ) : ℚ) := by
      have h1 : (0 : ℚ) < (a : ℚ) - 1 := by linarith
      have h2 : (0 : ℚ) < ((c + s.card : ℕ) : ℚ) := by
        rw [hcc2]; linarith [hcQ, hjQ]
      rw [div_le_iff₀ h1, div_mul_eq_mul_div, le_div_iff₀ h2]
      nlinarith [hmjQ, h1, h2, hBp]
    have hpos1 : (0 : ℚ) ≤ ∏ p ∈ s, ((p : ℚ) / ((p : ℚ) - 1)) := by
      apply Finset.prod_nonneg
      intro p hp
      apply div_nonneg (Nat.cast_nonneg _)
      have hple : c + 1 ≤ p := hsT p hp
      have h1p : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast (by omega : 1 ≤ p)
      linarith
    have hposB : (0 : ℚ) ≤ ((c + s.card + 1 : ℕ) : ℚ) / ((c + s.card : ℕ) : ℚ) := by
      apply div_nonneg (Nat.cast_nonneg _)
      have hlt : (0 : ℚ) ≤ ((c + s.card : ℕ) : ℚ) := by rw [hcc2]; linarith [hcQ, hjQ]
      linarith
    have hnonneg : (0 : ℚ) ≤ ((c + s.card : ℕ) : ℚ) / (c : ℚ) :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt hcQ)
    calc ((a : ℚ) / ((a : ℚ) - 1)) * (∏ p ∈ s, ((p : ℚ) / ((p : ℚ) - 1)))
        ≤ (((c + s.card + 1 : ℕ) : ℚ) / ((c + s.card : ℕ) : ℚ))
            * (((c + s.card : ℕ) : ℚ) / (c : ℚ)) :=
          mul_le_mul hmono hIH hpos1 hposB
      _ = ((c + s.card + 1 : ℕ) : ℚ) / (c : ℚ) := by
          have h2ne : ((c + s.card : ℕ) : ℚ) ≠ 0 := by
            have hlt : (0 : ℚ) < ((c + s.card : ℕ) : ℚ) := by rw [hcc2]; linarith [hcQ, hjQ]
            linarith
          field_simp

/-- Each abundancy correction factor lies strictly between zero and one. -/
private theorem correction_mem_Ioo (p a : ℕ) (hp : p.Prime) :
    0 < 1 - 1 / (p : ℚ) ^ (a + 1) ∧ 1 - 1 / (p : ℚ) ^ (a + 1) < 1 := by
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  have hle : (p : ℚ) ≤ (p : ℚ) ^ (a + 1) := by
    conv_lhs => rw [← pow_one (p : ℚ)]
    apply pow_le_pow_right₀ (by linarith) (by omega)
  have hx1 : (1 : ℚ) < (p : ℚ) ^ (a + 1) := by linarith
  have hx0 : (0 : ℚ) < (p : ℚ) ^ (a + 1) := by linarith
  constructor
  · have h : (1 : ℚ) / (p : ℚ) ^ (a + 1) < 1 := by
      rw [div_lt_one hx0]
      exact hx1
    linarith
  · have h : (0 : ℚ) < (1 : ℚ) / (p : ℚ) ^ (a + 1) := one_div_pos.mpr hx0
    linarith

/-- The supremum bound exceeds two for a non-deficient number. -/
private theorem abundancySup_gt_two (n p₁ : ℕ) (hn : IsNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors) : 2 < abundancySup n := by
  obtain ⟨hn0, hsum⟩ := hn
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hne : n.primeFactors.Nonempty := ⟨p₁, hp₁⟩
  have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hnpos
  have hHge : 2 ≤ abundancyIndex n := by
    rw [abundancyIndex, le_div_iff₀ hnQ]
    exact_mod_cast hsum
  have hQpos : 0 < abundancySup n := by
    simp only [abundancySup]
    apply Finset.prod_pos
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hpp.two_le
    apply div_pos (by linarith) (by linarith)
  have hP1 : ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ (n.factorization p + 1)) < 1 := by
    have h := Finset.prod_lt_prod_of_nonempty₀ (s := n.primeFactors)
      (f := fun p : ℕ => 1 - 1 / (p : ℚ) ^ (n.factorization p + 1))
      (g := fun _ : ℕ => (1 : ℚ))
      (fun p hp => (correction_mem_Ioo p _ ((Nat.mem_primeFactors.mp hp).1)).1)
      (fun p hp => (correction_mem_Ioo p _ ((Nat.mem_primeFactors.mp hp).1)).2)
      hne
    simpa using h
  have hE := abundancyIndex_eq_sup_mul n hn0
  rw [hE] at hHge
  have hlt : abundancySup n * ∏ p ∈ n.primeFactors,
      (1 - 1 / (p : ℚ) ^ (n.factorization p + 1)) < abundancySup n * 1 :=
    mul_lt_mul_of_pos_left hP1 hQpos
  rw [mul_one] at hlt
  linarith [hHge, hlt]

/-- The least prime factor does not exceed the number of distinct prime factors. -/
private theorem least_prime_le_card (n p₁ : ℕ) (hn : IsNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors) (hmin : ∀ q ∈ n.primeFactors, p₁ ≤ q) :
    p₁ ≤ n.primeFactors.card := by
  have hpp : p₁.Prime := (Nat.mem_primeFactors.mp hp₁).1
  have hp12 : 2 ≤ p₁ := hpp.two_le
  have hH2 : 2 < abundancySup n := abundancySup_gt_two n p₁ hn hp₁
  have hTele := prod_div_sub_one_le n.primeFactors (p₁ - 1) (by omega)
    (fun p hp => by have hle := hmin p hp; omega)
  simp only [abundancySup] at hH2
  by_contra hcon
  have hlt : n.primeFactors.card < p₁ := not_le.mp hcon
  have hpos : (0 : ℚ) < ((p₁ - 1 : ℕ) : ℚ) := by
    have h1 : 0 < p₁ - 1 := by omega
    exact_mod_cast h1
  have hle : ((p₁ - 1 + n.primeFactors.card : ℕ) : ℚ) / ((p₁ - 1 : ℕ) : ℚ) ≤ 2 := by
    rw [div_le_iff₀ hpos]
    have hnat : p₁ - 1 + n.primeFactors.card ≤ 2 * (p₁ - 1) := by omega
    exact_mod_cast hnat
  linarith [hTele, hle, hH2]

/-- An odd non-deficient number has at least two distinct prime factors. -/
private theorem two_le_card_primeFactors (n p₁ : ℕ) (hno : Odd n)
    (hn : IsNondeficient n) (hp₁ : p₁ ∈ n.primeFactors)
    (hmin : ∀ q ∈ n.primeFactors, p₁ ≤ q) : 2 ≤ n.primeFactors.card := by
  have h3 := three_le_of_mem_primeFactors n p₁ hno hp₁
  have hle := least_prime_le_card n p₁ hn hp₁ hmin
  omega

/-- The phi-product over prime factors is positive. -/
private theorem phi_prod_pos (n : ℕ) :
    0 < ∏ p ∈ n.primeFactors, (p - 1) := by
  apply Finset.prod_pos
  intro p hp
  have h2 := (Nat.mem_primeFactors.mp hp).1.two_le
  omega

/-- The radical is positive. -/
private theorem radical_pos (n : ℕ) : 0 < ∏ q ∈ n.primeFactors, q := by
  apply Finset.prod_pos
  intro q hq
  exact (Nat.mem_primeFactors.mp hq).1.pos

/-- The supremum bound as a quotient of the radical by the phi-product. -/
private theorem sup_eq_div (n : ℕ) :
    abundancySup n = ((∏ q ∈ n.primeFactors, q : ℕ) : ℚ)
      / ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℚ) := by
  have hcast : ∀ p ∈ n.primeFactors, ((p : ℚ) - 1) = (((p - 1 : ℕ)) : ℚ) := by
    intro p hp
    have hpp := (Nat.mem_primeFactors.mp hp).1
    rw [Nat.cast_sub hpp.one_le]
    simp
  simp only [abundancySup, Finset.prod_div_distrib]
  congr 1
  · exact (Nat.cast_prod _ _).symm
  · rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    exact hcast p hp

/-- The radical exceeds twice the phi-product for a non-deficient number. -/
private theorem radical_gt_two_mul_phi (n p₁ : ℕ) (hn : IsNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors) :
    2 * ∏ p ∈ n.primeFactors, (p - 1) < ∏ q ∈ n.primeFactors, q := by
  have hH2 := abundancySup_gt_two n p₁ hn hp₁
  have hdiv := sup_eq_div n
  rw [hdiv] at hH2
  have hphi : (0 : ℚ) < ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℚ) := by
    exact_mod_cast phi_prod_pos n
  have hlt : (2 : ℚ) * ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℚ)
      < ((∏ q ∈ n.primeFactors, q : ℕ) : ℚ) :=
    (lt_div_iff₀ hphi).mp hH2
  exact_mod_cast hlt

/-- The excess is congruent to twice the cofactor phi-product modulo the largest prime. -/
private theorem excess_modEq_max_prime (n pK : ℕ) (hpK : pK ∈ n.primeFactors)
    (hle : 2 * ∏ p ∈ n.primeFactors, (p - 1) ≤ ∏ q ∈ n.primeFactors, q) :
    ((((∏ q ∈ n.primeFactors, q) - 2 * ∏ p ∈ n.primeFactors, (p - 1) : ℕ)) : ℤ)
      ≡ 2 * (((∏ p ∈ n.primeFactors.erase pK, (p - 1) : ℕ)) : ℤ)
      [ZMOD (pK : ℤ)] := by
  have hpp : pK.Prime := (Nat.mem_primeFactors.mp hpK).1
  have hR : ∏ q ∈ n.primeFactors, q
      = pK * ∏ q ∈ n.primeFactors.erase pK, q :=
    (Finset.mul_prod_erase _ _ hpK).symm
  have hPhi : ∏ p ∈ n.primeFactors, (p - 1)
      = (pK - 1) * ∏ p ∈ n.primeFactors.erase pK, (p - 1) :=
    (Finset.mul_prod_erase _ _ hpK).symm
  have hx : ((((∏ q ∈ n.primeFactors, q) - 2 * ∏ p ∈ n.primeFactors, (p - 1) : ℕ)) : ℤ)
      = ((∏ q ∈ n.primeFactors, q : ℕ) : ℤ)
        - 2 * ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle, Nat.cast_mul]
    simp
  rw [hx, hR, hPhi, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hpp.one_le]
  simp only [Nat.cast_one]
  rw [Int.modEq_iff_dvd]
  use 2 * (((∏ p ∈ n.primeFactors.erase pK, (p - 1) : ℕ)) : ℤ)
    - (((∏ q ∈ n.primeFactors.erase pK, q : ℕ)) : ℤ)
  push_cast
  ring

/-- If the excess is small, the largest prime is below the square root of the radical. -/
private theorem max_prime_lt_sqrt_of_excess_lt (n pK : ℕ)
    (hpK : pK ∈ n.primeFactors)
    (hlt : 2 * ∏ p ∈ n.primeFactors, (p - 1) < ∏ q ∈ n.primeFactors, q)
    (hx : (∏ q ∈ n.primeFactors, q) - 2 * ∏ p ∈ n.primeFactors, (p - 1)
      < 2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1))
    (hH2 : (2 : ℚ) < abundancySup n) :
    (pK : ℝ) < Real.sqrt ((∏ q ∈ n.primeFactors, q : ℕ) : ℝ) := by
  have hpp : pK.Prime := (Nat.mem_primeFactors.mp hpK).1
  have hpp1 : 1 ≤ pK := hpp.one_le
  have hpK2 : 2 ≤ pK := hpp.two_le
  have hle : 2 * ∏ p ∈ n.primeFactors, (p - 1) ≤ ∏ q ∈ n.primeFactors, q :=
    le_of_lt hlt
  have hmod := excess_modEq_max_prime n pK hpK hle
  have hR : ∏ q ∈ n.primeFactors, q
      = pK * ∏ q ∈ n.primeFactors.erase pK, q :=
    (Finset.mul_prod_erase _ _ hpK).symm
  have hPhi : ∏ p ∈ n.primeFactors, (p - 1)
      = (pK - 1) * ∏ p ∈ n.primeFactors.erase pK, (p - 1) :=
    (Finset.mul_prod_erase _ _ hpK).symm
  have hPhi'1 : 1 ≤ ∏ p ∈ n.primeFactors.erase pK, (p - 1) := by
    apply Finset.one_le_prod
    intro p hp
    have hmem : p ∈ n.primeFactors := Finset.mem_of_mem_erase hp
    have h2 := (Nat.mem_primeFactors.mp hmem).1.two_le
    omega
  have hle2 : (∏ q ∈ n.primeFactors, q) - 2 * ∏ p ∈ n.primeFactors, (p - 1)
      ≤ 2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1) := le_of_lt hx
  have hcast : ((((2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1))
      - ((∏ q ∈ n.primeFactors, q) - 2 * ∏ p ∈ n.primeFactors, (p - 1)) : ℕ)) : ℤ)
      = 2 * (((∏ p ∈ n.primeFactors.erase pK, (p - 1) : ℕ)) : ℤ)
        - ((((∏ q ∈ n.primeFactors, q) - 2 * ∏ p ∈ n.primeFactors, (p - 1) : ℕ)) : ℤ) := by
    rw [Nat.cast_sub hle2, Nat.cast_mul]
    simp
  have hdvdZ : (pK : ℤ)
      ∣ ((((2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1))
        - ((∏ q ∈ n.primeFactors, q) - 2 * ∏ p ∈ n.primeFactors, (p - 1)) : ℕ)) : ℤ) := by
    rw [hcast]
    exact hmod.dvd
  have hdvd : pK ∣ (2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1))
      - ((∏ q ∈ n.primeFactors, q) - 2 * ∏ p ∈ n.primeFactors, (p - 1)) :=
    Int.natCast_dvd_natCast.mp hdvdZ
  have hx1 : 1 ≤ (∏ q ∈ n.primeFactors, q) - 2 * ∏ p ∈ n.primeFactors, (p - 1) := by
    omega
  have hposd : 0 < (2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1))
      - ((∏ q ∈ n.primeFactors, q) - 2 * ∏ p ∈ n.primeFactors, (p - 1)) := by
    omega
  have hpltNat : pK < 2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1) := by
    have hle3 := Nat.le_of_dvd hposd hdvd
    omega
  have hR''pos : (0 : ℚ) < ((∏ q ∈ n.primeFactors.erase pK, q : ℕ) : ℚ) := by
    have hposN : 0 < ∏ q ∈ n.primeFactors.erase pK, q := by
      apply Finset.prod_pos
      intro q hq
      exact (Nat.mem_primeFactors.mp (Finset.mem_of_mem_erase hq)).1.pos
    exact_mod_cast hposN
  have hpKpos : (0 : ℚ) < (pK : ℚ) := by exact_mod_cast hpp.pos
  have hpK0 : (pK : ℚ) ≠ 0 := ne_of_gt hpKpos
  have hR''0 : ((∏ q ∈ n.primeFactors.erase pK, q : ℕ) : ℚ) ≠ 0 := ne_of_gt hR''pos
  have hsubpos : (0 : ℚ) < (pK : ℚ) - 1 := by
    have h2 : (2 : ℚ) ≤ (pK : ℚ) := by exact_mod_cast hpK2
    linarith
  have hsub0 : (pK : ℚ) - 1 ≠ 0 := ne_of_gt hsubpos
  have heq14 : ((2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1) : ℕ) : ℚ)
      = 2 * (((∏ q ∈ n.primeFactors, q : ℕ) : ℚ) / (pK : ℚ))
        * (∏ p ∈ n.primeFactors.erase pK, (((p - 1 : ℕ)) : ℚ) / (p : ℚ)) := by
    have hH'' : (∏ p ∈ n.primeFactors.erase pK, (((p - 1 : ℕ)) : ℚ) / (p : ℚ))
        = ((∏ p ∈ n.primeFactors.erase pK, (p - 1) : ℕ) : ℚ)
          / ((∏ q ∈ n.primeFactors.erase pK, q : ℕ) : ℚ) := by
      rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod]
    rw [hH'']
    have hRcast : ((∏ q ∈ n.primeFactors, q : ℕ) : ℚ)
        = (pK : ℚ) * ((∏ q ∈ n.primeFactors.erase pK, q : ℕ) : ℚ) := by
      exact_mod_cast hR
    have e1 : ((2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1) : ℕ) : ℚ)
        = 2 * ((∏ p ∈ n.primeFactors.erase pK, (p - 1) : ℕ) : ℚ) := by
      push_cast
      ring
    rw [hRcast, e1]
    field_simp
  have hHsplit : abundancySup n
      = (∏ p ∈ n.primeFactors.erase pK, ((p : ℚ) / ((p : ℚ) - 1)))
        * ((pK : ℚ) / ((pK : ℚ) - 1)) := by
    simp only [abundancySup]
    rw [← Finset.mul_prod_erase _ _ hpK, mul_comm]
  have hfrac_pos : (0 : ℚ) < (pK : ℚ) / ((pK : ℚ) - 1) :=
    div_pos hpKpos hsubpos
  have hH'pos : (0 : ℚ) < ∏ p ∈ n.primeFactors.erase pK, ((p : ℚ) / ((p : ℚ) - 1)) := by
    apply Finset.prod_pos
    intro p hp
    have hmem : p ∈ n.primeFactors := Finset.mem_of_mem_erase hp
    have h2 : (2 : ℚ) ≤ (p : ℚ) :=
      by exact_mod_cast (Nat.mem_primeFactors.mp hmem).1.two_le
    apply div_pos (by linarith) (by linarith)
  have h2 : (2 : ℚ) < (∏ p ∈ n.primeFactors.erase pK, ((p : ℚ) / ((p : ℚ) - 1)))
      * ((pK : ℚ) / ((pK : ℚ) - 1)) := by
    rw [← hHsplit]
    exact hH2
  have heqD : 2 * ((pK : ℚ) - 1) / (pK : ℚ)
      = 2 / ((pK : ℚ) / ((pK : ℚ) - 1)) := by
    field_simp
  have hgt : 2 * ((pK : ℚ) - 1) / (pK : ℚ)
      < ∏ p ∈ n.primeFactors.erase pK, ((p : ℚ) / ((p : ℚ) - 1)) := by
    rw [heqD, div_lt_iff₀ hfrac_pos]
    exact h2
  have hterm : ∀ p ∈ n.primeFactors.erase pK,
      (((p - 1 : ℕ)) : ℚ) / (p : ℚ) = ((p : ℚ) / ((p : ℚ) - 1))⁻¹ := by
    intro p hp
    have hmem : p ∈ n.primeFactors := Finset.mem_of_mem_erase hp
    have h1 : (1 : ℕ) ≤ p := (Nat.mem_primeFactors.mp hmem).1.one_le
    rw [Nat.cast_sub h1, Nat.cast_one, inv_div]
  have hH''eq : (∏ p ∈ n.primeFactors.erase pK, (((p - 1 : ℕ)) : ℚ) / (p : ℚ))
      = (∏ p ∈ n.primeFactors.erase pK, ((p : ℚ) / ((p : ℚ) - 1)))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    exact hterm p hp
  have heq2 : ((1 : ℚ) / 2) * ((pK : ℚ) / ((pK : ℚ) - 1))
      = 1 / (2 * ((pK : ℚ) - 1) / (pK : ℚ)) := by
    field_simp
  have hXpos : (0 : ℚ) < 2 * ((pK : ℚ) - 1) / (pK : ℚ) :=
    div_pos (mul_pos (by norm_num) hsubpos) hpKpos
  have h15 : (∏ p ∈ n.primeFactors.erase pK, (((p - 1 : ℕ)) : ℚ) / (p : ℚ))
      < ((1 : ℚ) / 2) * ((pK : ℚ) / ((pK : ℚ) - 1)) := by
    rw [hH''eq, heq2, ← one_div]
    exact one_div_lt_one_div_of_lt hXpos hgt
  have h2Rpos : (0 : ℚ) < 2 * (((∏ q ∈ n.primeFactors, q : ℕ) : ℚ) / (pK : ℚ)) := by
    have hRpos : (0 : ℚ) < ((∏ q ∈ n.primeFactors, q : ℕ) : ℚ) := by
      exact_mod_cast radical_pos n
    exact mul_pos (by norm_num) (div_pos hRpos hpKpos)
  have hfin : (pK : ℚ) < ((∏ q ∈ n.primeFactors, q : ℕ) : ℚ) / ((pK : ℚ) - 1) := by
    have hcastQ : (pK : ℚ) < ((2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1) : ℕ) : ℚ) := by
      exact_mod_cast hpltNat
    rw [heq14] at hcastQ
    have hmul := mul_lt_mul_of_pos_left h15 h2Rpos
    have heq3 : 2 * (((∏ q ∈ n.primeFactors, q : ℕ) : ℚ) / (pK : ℚ))
        * (((1 : ℚ) / 2) * ((pK : ℚ) / ((pK : ℚ) - 1)))
        = ((∏ q ∈ n.primeFactors, q : ℕ) : ℚ) / ((pK : ℚ) - 1) := by
      field_simp
    rw [heq3] at hmul
    exact lt_trans hcastQ hmul
  have h16Q : (pK : ℚ) * ((pK : ℚ) - 1) < ((∏ q ∈ n.primeFactors, q : ℕ) : ℚ) :=
    (lt_div_iff₀ hsubpos).mp hfin
  have h16 : pK * (pK - 1) < ∏ q ∈ n.primeFactors, q := by
    have hcast2 : ((pK * (pK - 1) : ℕ) : ℚ) = (pK : ℚ) * ((pK : ℚ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hpp1]
      simp
    rw [← hcast2] at h16Q
    exact_mod_cast h16Q
  have hRsq : pK ^ 2 ≤ ∏ q ∈ n.primeFactors, q := by
    have hdvdR : pK ∣ ∏ q ∈ n.primeFactors, q := Finset.dvd_prod_of_mem _ hpK
    have hdvdS : pK ∣ pK * (pK - 1) := dvd_mul_right pK (pK - 1)
    have hdvdD : pK ∣ (∏ q ∈ n.primeFactors, q) - pK * (pK - 1) :=
      Nat.dvd_sub hdvdR hdvdS
    obtain ⟨t, ht⟩ := hdvdD
    have hpos2 : 0 < (∏ q ∈ n.primeFactors, q) - pK * (pK - 1) := by omega
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | hpos3
      · simp at ht
        omega
      · exact hpos3
    have hRdecomp : ∏ q ∈ n.primeFactors, q = pK * (pK - 1) + pK * t := by
      have h := Nat.add_sub_cancel' (le_of_lt h16)
      rw [ht] at h
      exact h.symm
    have hpow : pK ^ 2 = pK * pK := by ring
    rw [hRdecomp, hpow]
    have h1 : pK * 1 ≤ pK * t := mul_le_mul_of_nonneg_left ht1 (Nat.zero_le _)
    have hsplit : pK * pK = pK * (pK - 1) + pK * 1 := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hpp1]
    rw [hsplit]
    exact Nat.add_le_add_left h1 _
  have hRne : ∏ q ∈ n.primeFactors, q ≠ pK ^ 2 := by
    intro hcon
    rw [hR] at hcon
    have hRe : ∏ q ∈ n.primeFactors.erase pK, q = pK := by
      have h2eq : pK * ∏ q ∈ n.primeFactors.erase pK, q = pK * pK := by
        rw [← pow_two]
        exact hcon
      exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hpp.ne_zero) h2eq
    have hempty : n.primeFactors.erase pK = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro q hq
      have hmem : q ∈ n.primeFactors := Finset.mem_of_mem_erase hq
      have hne : q ≠ pK := Finset.ne_of_mem_erase hq
      have hqq : q.Prime := (Nat.mem_primeFactors.mp hmem).1
      have hdvd : q ∣ pK := by
        rw [← hRe]
        exact Finset.dvd_prod_of_mem _ hq
      rcases (Nat.dvd_prime hpp).mp hdvd with h1 | heq
      · have h2q := hqq.two_le
        omega
      · exact hne heq
    have h1prod : ∏ q ∈ n.primeFactors.erase pK, q = 1 := by
      rw [hempty, Finset.prod_empty]
    have h2K := hpp.two_le
    omega
  have hlt2 : pK ^ 2 < ∏ q ∈ n.primeFactors, q := lt_of_le_of_ne' hRsq hRne
  have hltR : (pK : ℝ) ^ 2 < ((∏ q ∈ n.primeFactors, q : ℕ) : ℝ) := by
    exact_mod_cast hlt2
  exact Real.lt_sqrt_of_sq_lt hltR

/-- A product of two consecutive integers, both above one, is not a prime power. -/
private theorem prime_pow_ne_card_mul_succ (q e k : ℕ) (hq : q.Prime)
    (hk : 2 ≤ k) : q ^ e ≠ k * (k + 1) := by
  intro hcon
  have hk_dvd : k ∣ q ^ e := ⟨k + 1, hcon⟩
  have hk1_dvd : k + 1 ∣ q ^ e := ⟨k, by rw [hcon]; ring⟩
  obtain ⟨s, _, hs_eq⟩ := (Nat.dvd_prime_pow hq).mp hk_dvd
  obtain ⟨t, _, ht_eq⟩ := (Nat.dvd_prime_pow hq).mp hk1_dvd
  have hs1 : 1 ≤ s := by
    by_contra hc
    have hs0 : s = 0 := by omega
    rw [hs0] at hs_eq
    simp at hs_eq
    omega
  have ht0 : t ≠ 0 := by
    intro ht0
    rw [ht0, pow_zero] at ht_eq
    omega
  have hq_s : q ∣ q ^ s := dvd_pow_self q (by omega : s ≠ 0)
  have hq_t : q ∣ q ^ t := dvd_pow_self q ht0
  have hsub : q ^ t - q ^ s = 1 := by omega
  have hdvd1 : q ∣ 1 := by
    have h := Nat.dvd_sub hq_t hq_s
    rw [hsub] at h
    exact h
  have hq1 : q = 1 := Nat.dvd_one.mp hdvd1
  have hq2 := hq.two_le
  omega

/-- A prime power component attaining the minimum. -/
private theorem exists_min_pow (n : ℕ) (hne : n.primeFactors.Nonempty) :
    ∃ p₀ ∈ n.primeFactors, ∀ p ∈ n.primeFactors,
      p₀ ^ (n.factorization p₀ + 1) ≤ p ^ (n.factorization p + 1) := by
  set T : Set ℕ := {y | ∃ p ∈ n.primeFactors, p ^ (n.factorization p + 1) = y}
    with hT
  have hTne : T.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p ^ (n.factorization p + 1), p, hp, rfl⟩
  have hmem : sInf T ∈ T := Nat.sInf_mem hTne
  obtain ⟨p₀, hp₀, hmin⟩ := hmem
  refine ⟨p₀, hp₀, fun p hp => ?_⟩
  have hle : sInf T ≤ p ^ (n.factorization p + 1) := Nat.sInf_le ⟨p, hp, rfl⟩
  omega

/-- The correction product is at least `1 - k * m`. -/
private theorem prod_correction_ge (n : ℕ) (m : ℚ)
    (hm1 : m ≤ 1)
    (hle : ∀ p ∈ n.primeFactors, 1 / (p : ℚ) ^ (n.factorization p + 1) ≤ m) :
    1 - (n.primeFactors.card : ℚ) * m
      ≤ ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ (n.factorization p + 1)) := by
  have h1 : ((1 - m) ^ n.primeFactors.card : ℚ)
      ≤ ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ (n.factorization p + 1)) := by
    have hprod : (∏ _p ∈ n.primeFactors, (1 - m))
        = ((1 - m) ^ n.primeFactors.card : ℚ) :=
      Finset.prod_const _
    rw [← hprod]
    apply Finset.prod_le_prod₀
    · intro p _
      linarith [hm1]
    · intro p hp
      linarith [hle p hp]
  have hbern : 1 - (n.primeFactors.card : ℚ) * m ≤ (1 - m) ^ n.primeFactors.card := by
    have h := one_add_mul_le_pow (show (-2 : ℚ) ≤ -m by linarith)
      n.primeFactors.card
    have e1 : (1 : ℚ) + (n.primeFactors.card : ℚ) * (-m)
        = 1 - (n.primeFactors.card : ℚ) * m := by ring
    have e2 : (1 + -m : ℚ) = 1 - m := by ring
    rw [e1, e2] at h
    exact h
  exact le_trans hbern h1

/-- Abundancy is bounded above via primitivity at `n / p₁`. -/
private theorem abundancy_lt_two_mul (n p₁ : ℕ) (hn : IsPrimitiveNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors) (m : ℚ)
    (hm : 1 / (p₁ : ℚ) ^ n.factorization p₁ ≤ (p₁ : ℚ) * m) :
    abundancyIndex n < 2 * (1 + (p₁ : ℚ) * m) := by
  obtain ⟨⟨hn0, _⟩, hproper⟩ := hn
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hpp : p₁.Prime := (Nat.mem_primeFactors.mp hp₁).1
  have hdvd : p₁ ∣ n := Nat.dvd_of_mem_primeFactors hp₁
  have hmem : n / p₁ ∈ Nat.divisors n :=
    Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hn0⟩
  have hlt : n / p₁ < n := Nat.div_lt_self hnpos hpp.one_lt
  have hdef := hproper (n / p₁) hmem hlt
  have hnposd : 0 < n / p₁ := Nat.div_pos (Nat.le_of_dvd hnpos hdvd) hpp.pos
  have hnposdQ : (0 : ℚ) < ((n / p₁ : ℕ) : ℚ) := by exact_mod_cast hnposd
  have h2 : abundancyIndex (n / p₁) < 2 := by
    rw [abundancyIndex, div_lt_iff₀ hnposdQ]
    exact_mod_cast hdef
  have hposd : 0 < abundancyIndex (n / p₁) := abundancyIndex_pos _ hnposd
  have ha1 : 1 ≤ n.factorization p₁ := by
    have hpos := Nat.Prime.factorization_pos_of_dvd hpp hn0 hdvd
    omega
  have hratio := abundancyIndex_div_le n p₁ (n.factorization p₁) hnpos hpp ha1 rfl
  have h1a : (0 : ℚ) < 1 + 1 / (p₁ : ℚ) ^ n.factorization p₁ := by
    have hpos1 : (0 : ℚ) < 1 / (p₁ : ℚ) ^ n.factorization p₁ := by
      apply one_div_pos.mpr
      apply pow_pos
      exact_mod_cast hpp.pos
    linarith
  have hdecomp : abundancyIndex n
      = (abundancyIndex n / abundancyIndex (n / p₁)) * abundancyIndex (n / p₁) :=
    (div_mul_cancel₀ _ hposd.ne').symm
  have hle2 : (abundancyIndex n / abundancyIndex (n / p₁)) * abundancyIndex (n / p₁)
      ≤ (1 + 1 / (p₁ : ℚ) ^ n.factorization p₁) * abundancyIndex (n / p₁) :=
    mul_le_mul_of_nonneg_right hratio (le_of_lt hposd)
  have hlt2 : (1 + 1 / (p₁ : ℚ) ^ n.factorization p₁) * abundancyIndex (n / p₁)
      < (1 + 1 / (p₁ : ℚ) ^ n.factorization p₁) * 2 :=
    mul_lt_mul_of_pos_left h2 h1a
  have hle3 : (1 + 1 / (p₁ : ℚ) ^ n.factorization p₁) * 2 ≤ (1 + (p₁ : ℚ) * m) * 2 := by
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith [hm]
  have heq : (1 + (p₁ : ℚ) * m) * 2 = 2 * (1 + (p₁ : ℚ) * m) := by ring
  calc abundancyIndex n
      = (abundancyIndex n / abundancyIndex (n / p₁)) * abundancyIndex (n / p₁) :=
        hdecomp
    _ ≤ (1 + 1 / (p₁ : ℚ) ^ n.factorization p₁) * abundancyIndex (n / p₁) := hle2
    _ < (1 + 1 / (p₁ : ℚ) ^ n.factorization p₁) * 2 := hlt2
    _ ≤ (1 + (p₁ : ℚ) * m) * 2 := hle3
    _ = 2 * (1 + (p₁ : ℚ) * m) := heq

/-- A small prime power component from a large excess. -/
private theorem exists_small_component (n p₁ pK : ℕ) (hno : Odd n)
    (hn : IsPrimitiveNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors) (hmin : ∀ q ∈ n.primeFactors, p₁ ≤ q)
    (hpK : pK ∈ n.primeFactors) (hmax : ∀ q ∈ n.primeFactors, q ≤ pK)
    (hbig : 2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1)
      ≤ (∏ q ∈ n.primeFactors, q) - 2 * ∏ p ∈ n.primeFactors, (p - 1)) :
    ∃ p ∈ n.primeFactors,
      p ^ (n.factorization p + 1)
        < (n.primeFactors.card + 2 + p₁) * (pK - 1) := by
  obtain ⟨hn0, _⟩ := hn.1
  have hppK : pK.Prime := (Nat.mem_primeFactors.mp hpK).1
  have hpK2 : 2 ≤ pK := hppK.two_le
  have hpp1 : p₁.Prime := (Nat.mem_primeFactors.mp hp₁).1
  have hk2 : 2 ≤ n.primeFactors.card :=
    two_le_card_primeFactors n p₁ hno hn.1 hp₁ hmin
  have hplek : p₁ ≤ n.primeFactors.card := least_prime_le_card n p₁ hn.1 hp₁ hmin
  have hne : n.primeFactors.Nonempty := ⟨p₁, hp₁⟩
  set k := n.primeFactors.card with hkdef
  have hsubpos : (0 : ℚ) < (pK : ℚ) - 1 := by
    have h2 : (2 : ℚ) ≤ (pK : ℚ) := by exact_mod_cast hpK2
    linarith
  have hsub0 : (pK : ℚ) - 1 ≠ 0 := ne_of_gt hsubpos
  set α : ℚ := 2 / ((pK : ℚ) - 1) with hαdef
  have hα0 : (0 : ℚ) < α := by
    rw [hαdef]
    exact div_pos (by norm_num) hsubpos
  have hRge : 2 * ∏ p ∈ n.primeFactors, (p - 1)
      + 2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1)
      ≤ ∏ q ∈ n.primeFactors, q := by
    have h := Nat.add_sub_cancel'
      (le_of_lt (radical_gt_two_mul_phi n p₁ hn.1 hp₁))
    omega
  have hPhi : ∏ p ∈ n.primeFactors, (p - 1)
      = (pK - 1) * ∏ p ∈ n.primeFactors.erase pK, (p - 1) :=
    (Finset.mul_prod_erase _ _ hpK).symm
  have hPhicast : ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℚ)
      = ((pK : ℚ) - 1) * ((∏ p ∈ n.primeFactors.erase pK, (p - 1) : ℕ) : ℚ) := by
    rw [hPhi, Nat.cast_mul, Nat.cast_sub hppK.one_le, Nat.cast_one]
  have hHge : 2 + α ≤ abundancySup n := by
    have hdiv := sup_eq_div n
    rw [hdiv]
    have hphi : (0 : ℚ) < ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℚ) := by
      exact_mod_cast phi_prod_pos n
    rw [le_div_iff₀ hphi, hPhicast]
    have heq : ((2 : ℚ) + α) * (((pK : ℚ) - 1)
        * ((∏ p ∈ n.primeFactors.erase pK, (p - 1) : ℕ) : ℚ))
        = 2 * (pK : ℚ) * ((∏ p ∈ n.primeFactors.erase pK, (p - 1) : ℕ) : ℚ) := by
      rw [hαdef]
      field_simp
      ring
    have heq' : (2 : ℚ) * (pK : ℚ)
        * ((∏ p ∈ n.primeFactors.erase pK, (p - 1) : ℕ) : ℚ)
        = 2 * ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℚ)
          + 2 * ((∏ p ∈ n.primeFactors.erase pK, (p - 1) : ℕ) : ℚ) := by
      rw [hPhicast]
      ring
    rw [heq, heq']
    exact_mod_cast hRge
  obtain ⟨p₀, hp₀, hmin⟩ := exists_min_pow n hne
  have hpp0 : p₀.Prime := (Nat.mem_primeFactors.mp hp₀).1
  set M := p₀ ^ (n.factorization p₀ + 1) with hMdef
  set m : ℚ := 1 / (M : ℚ) with hmdef
  have hM2 : 2 ≤ M := by
    have h2p : 2 ≤ p₀ := hpp0.two_le
    have hle : p₀ ≤ p₀ ^ (n.factorization p₀ + 1) :=
      le_self_pow (by omega : 1 ≤ p₀) (by omega : n.factorization p₀ + 1 ≠ 0)
    rw [← hMdef] at hle
    omega
  have hMpos : (0 : ℚ) < (M : ℚ) := by
    have h0 : 0 < M := by omega
    exact_mod_cast h0
  have hM0 : (M : ℚ) ≠ 0 := ne_of_gt hMpos
  have hm0 : (0 : ℚ) < m := by
    rw [hmdef]
    exact one_div_pos.mpr hMpos
  have hm1 : m ≤ 1 := by
    rw [hmdef, div_le_one hMpos]
    have h1 : 1 ≤ M := by omega
    exact_mod_cast h1
  have hle : ∀ p ∈ n.primeFactors, 1 / (p : ℚ) ^ (n.factorization p + 1) ≤ m := by
    intro p hp
    rw [hmdef]
    have hleN := hmin p hp
    have hleQ : (M : ℚ) ≤ ((p ^ (n.factorization p + 1) : ℕ) : ℚ) := by
      exact_mod_cast hleN
    have hcast : ((p ^ (n.factorization p + 1) : ℕ) : ℚ)
        = (p : ℚ) ^ (n.factorization p + 1) := Nat.cast_pow _ _
    rw [hcast] at hleQ
    exact one_div_le_one_div_of_le hMpos hleQ
  have hkpos : (0 : ℚ) < (k : ℚ) := by
    have h0 : 0 < k := by omega
    exact_mod_cast h0
  have hQpos : (0 : ℚ) < abundancySup n := by
    simp only [abundancySup]
    apply Finset.prod_pos
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hpp.two_le
    apply div_pos (by linarith) (by linarith)
  by_cases hkm : (1 : ℚ) ≤ (k : ℚ) * m
  · have hMk : (M : ℚ) ≤ (k : ℚ) := by
      by_contra hcon
      have hgt : (k : ℚ) < (M : ℚ) := not_le.mp hcon
      have h1 : (1 : ℚ) / (M : ℚ) < 1 / (k : ℚ) :=
        one_div_lt_one_div_of_lt hkpos hgt
      have h2 : (k : ℚ) * ((1 : ℚ) / (M : ℚ)) < 1 := by
        have h3 := mul_lt_mul_of_pos_left h1 hkpos
        rw [mul_one_div_cancel hkpos.ne'] at h3
        exact h3
      rw [hmdef] at hkm
      linarith [h2, hkm]
    have hMleN : M ≤ k := by exact_mod_cast hMk
    have hblt : k < (k + 2 + p₁) * (pK - 1) := by
      have h1 : k + 1 ≤ k + 2 + p₁ := by omega
      have h2 : 1 ≤ pK - 1 := by omega
      have h3 : (k + 1) * 1 ≤ (k + 2 + p₁) * (pK - 1) :=
        mul_le_mul h1 h2 (Nat.zero_le _) (Nat.zero_le _)
      omega
    refine ⟨p₀, hp₀, ?_⟩
    rw [← hMdef]
    exact lt_of_le_of_lt hMleN hblt
  have hkm_lt : (k : ℚ) * m < 1 := not_le.mp hkm
  have h1km : (0 : ℚ) < 1 - (k : ℚ) * m := by linarith [hkm_lt]
  have hPlb : 1 - (k : ℚ) * m
      ≤ ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ (n.factorization p + 1)) :=
    prod_correction_ge n m hm1 hle
  have hE := abundancyIndex_eq_sup_mul n hn0
  have h_lower : (2 + α) * (1 - (k : ℚ) * m) ≤ abundancyIndex n := by
    rw [hE]
    exact mul_le_mul hHge hPlb (le_of_lt h1km) (le_of_lt hQpos)
  have heq1 : (1 : ℚ) / (p₁ : ℚ) ^ n.factorization p₁
      = (p₁ : ℚ) * (1 / (p₁ : ℚ) ^ (n.factorization p₁ + 1)) := by
    have hp10 : (p₁ : ℚ) ≠ 0 := by
      have hpos : 0 < p₁ := hpp1.pos
      exact_mod_cast (by omega : p₁ ≠ 0)
    have hpa0 : (p₁ : ℚ) ^ n.factorization p₁ ≠ 0 := pow_ne_zero _ hp10
    have hmul0 : (p₁ : ℚ) * (p₁ : ℚ) ^ n.factorization p₁ ≠ 0 :=
      mul_ne_zero hp10 hpa0
    rw [pow_succ']
    field_simp
  have hm2 : (1 : ℚ) / (p₁ : ℚ) ^ n.factorization p₁ ≤ (p₁ : ℚ) * m := by
    rw [heq1]
    apply mul_le_mul_of_nonneg_left (hle p₁ hp₁) (Nat.cast_nonneg _)
  have h_upper : abundancyIndex n < 2 * (1 + (p₁ : ℚ) * m) :=
    abundancy_lt_two_mul n p₁ hn hp₁ m hm2
  have hcomb : (2 + α) * (1 - (k : ℚ) * m) < 2 * (1 + (p₁ : ℚ) * m) :=
    lt_of_le_of_lt h_lower h_upper
  have hfrac : 1 + α / 2 < (1 + (p₁ : ℚ) * m) / (1 - (k : ℚ) * m) := by
    have hdiv : (2 + α) / 2 < (1 + (p₁ : ℚ) * m) / (1 - (k : ℚ) * m) := by
      rw [div_lt_div_iff₀ (by norm_num) h1km]
      linarith [hcomb]
    linarith [hdiv]
  by_cases hmcase : m < 1 / ((k : ℚ) * ((k : ℚ) + 1))
  · have hKM : 1 / (1 - (k : ℚ) * m) < 1 + ((k : ℚ) + 1) * m := by
      have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      have hm0R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
      have hmR : (m : ℝ) < 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
        have hcastR : ((m : ℚ) : ℝ)
            < (((1 : ℚ) / ((k : ℚ) * ((k : ℚ) + 1))) : ℝ) := by
          exact_mod_cast hmcase
        simpa using hcastR
      have h := one_div_one_sub_mul_lt_add (k : ℝ) (m : ℝ) hk2R hm0R hmR
      have hcastQ : ((((1 : ℚ) / (1 - (k : ℚ) * m)) : ℝ))
          < ((((1 : ℚ) + ((k : ℚ) + 1) * m) : ℝ)) := by
        simpa using h
      exact_mod_cast hcastQ
    have hpos1 : (0 : ℚ) < 1 + (p₁ : ℚ) * m := by
      have hp1nn : (0 : ℚ) ≤ (p₁ : ℚ) := Nat.cast_nonneg _
      have hnn := mul_nonneg hp1nn (le_of_lt hm0)
      linarith [hnn]
    have hfrac2 : (1 + (p₁ : ℚ) * m) / (1 - (k : ℚ) * m)
        < (1 + (p₁ : ℚ) * m) * (1 + ((k : ℚ) + 1) * m) := by
      have hmul := mul_lt_mul_of_pos_left hKM hpos1
      rw [div_eq_mul_one_div]
      exact hmul
    have hkey : (p₁ : ℚ) * ((k : ℚ) + 1) * m ^ 2 < m := by
      have hk1pos : (0 : ℚ) < (k : ℚ) + 1 := by linarith [hkpos]
      have hposK : (0 : ℚ) < (k : ℚ) * ((k : ℚ) + 1) := mul_pos hkpos hk1pos
      have hkk : (k : ℚ) * ((k : ℚ) + 1) * m < 1 := by
        have hlt := (lt_div_iff₀ hposK).mp hmcase
        linarith [hlt]
      have hple : (p₁ : ℚ) ≤ (k : ℚ) := by exact_mod_cast hplek
      have h1 : (p₁ : ℚ) * ((k : ℚ) + 1) * m ^ 2
          ≤ (k : ℚ) * ((k : ℚ) + 1) * m ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hple (le_of_lt hk1pos)) (sq_nonneg m)
      have h2 : (k : ℚ) * ((k : ℚ) + 1) * m ^ 2 < m := by
        have e : (k : ℚ) * ((k : ℚ) + 1) * m ^ 2
            = ((k : ℚ) * ((k : ℚ) + 1) * m) * m := by ring
        rw [e]
        have h3 := mul_lt_mul_of_pos_right hkk hm0
        rwa [one_mul] at h3
      linarith [h1, h2]
    have hchain : (1 + (p₁ : ℚ) * m) * (1 + ((k : ℚ) + 1) * m)
        < 1 + m * ((k : ℚ) + 2 + (p₁ : ℚ)) := by
      have ering : (1 + (p₁ : ℚ) * m) * (1 + ((k : ℚ) + 1) * m)
          = 1 + m * ((k : ℚ) + 1 + (p₁ : ℚ))
            + (p₁ : ℚ) * ((k : ℚ) + 1) * m ^ 2 := by ring
      have ering2 : (1 : ℚ) + m * ((k : ℚ) + 2 + (p₁ : ℚ))
          = 1 + m * ((k : ℚ) + 1 + (p₁ : ℚ)) + m := by ring
      rw [ering, ering2]
      linarith [hkey]
    have hcomb2 : (1 : ℚ) + α / 2 < 1 + m * ((k : ℚ) + 2 + (p₁ : ℚ)) :=
      lt_trans hfrac (lt_trans hfrac2 hchain)
    have hposS : (0 : ℚ) < (k : ℚ) + 2 + (p₁ : ℚ) := by
      have hk_nn : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg _
      have hp1nn : (0 : ℚ) ≤ (p₁ : ℚ) := Nat.cast_nonneg _
      linarith [hk_nn, hp1nn]
    have h2S : (0 : ℚ) < 2 * ((k : ℚ) + 2 + (p₁ : ℚ)) := mul_pos (by norm_num) hposS
    have hmalpha : α / (2 * ((k : ℚ) + 2 + (p₁ : ℚ))) < m := by
      have h1 : α / 2 < m * ((k : ℚ) + 2 + (p₁ : ℚ)) := by linarith [hcomb2]
      have h2 : α < 2 * (m * ((k : ℚ) + 2 + (p₁ : ℚ))) := by linarith [h1]
      have h3 : α / (2 * ((k : ℚ) + 2 + (p₁ : ℚ))) < m := by
        rw [div_lt_iff₀ h2S]
        linarith [h2]
      exact h3
    have hMm : (M : ℚ) = 1 / m := by
      rw [eq_div_iff hm0.ne']
      rw [hmdef]
      field_simp
    have hMlt : (M : ℚ) < 2 * ((k : ℚ) + 2 + (p₁ : ℚ)) / α := by
      rw [hMm, div_lt_div_iff₀ hm0 hα0]
      have h4 : α < m * (2 * ((k : ℚ) + 2 + (p₁ : ℚ))) :=
        (div_lt_iff₀ h2S).mp hmalpha
      linarith [h4]
    have hfinN : M < (k + 2 + p₁) * (pK - 1) := by
      have heqA : (2 : ℚ) * ((k : ℚ) + 2 + (p₁ : ℚ)) / α
          = (((k + 2 + p₁) * (pK - 1) : ℕ) : ℚ) := by
        rw [hαdef]
        have hcast : ((((k + 2 + p₁) * (pK - 1) : ℕ)) : ℚ)
            = ((k : ℚ) + 2 + (p₁ : ℚ)) * ((pK : ℚ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ pK)]
          push_cast
          ring
        rw [hcast]
        field_simp
      rw [heqA] at hMlt
      exact_mod_cast hMlt
    refine ⟨p₀, hp₀, ?_⟩
    rw [← hMdef]
    exact hfinN
  · have hmge : 1 / ((k : ℚ) * ((k : ℚ) + 1)) ≤ m := le_of_not_gt hmcase
    have hMle : (M : ℚ) ≤ (k : ℚ) * ((k : ℚ) + 1) := by
      have hKpos : (0 : ℚ) < (k : ℚ) * ((k : ℚ) + 1) :=
        mul_pos hkpos (by linarith [hkpos])
      by_contra hcon
      have hgt : (k : ℚ) * ((k : ℚ) + 1) < (M : ℚ) := not_le.mp hcon
      have h1 : (1 : ℚ) / (M : ℚ) < 1 / ((k : ℚ) * ((k : ℚ) + 1)) :=
        one_div_lt_one_div_of_lt hKpos hgt
      rw [hmdef] at hmge
      linarith [h1, hmge]
    have hMne : M ≠ k * (k + 1) := by
      rw [hMdef]
      exact prime_pow_ne_card_mul_succ p₀ _ k hpp0 hk2
    have hMltK : M < k * (k + 1) := by
      have hleN : M ≤ k * (k + 1) := by exact_mod_cast hMle
      exact lt_of_le_of_ne hleN hMne
    have hKle : k * (k + 1) ≤ (k + 2 + p₁) * (pK - 1) := by
      have hk1 : k + 1 ≤ k + 2 + p₁ := by omega
      have hk2' : k ≤ pK - 1 := by
        have hsub : n.primeFactors ⊆ Finset.Ico 2 (pK + 1) := by
          intro q hq
          simp only [Finset.mem_Ico]
          have h2q := (Nat.mem_primeFactors.mp hq).1.two_le
          have hleQ := hmax q hq
          omega
        have hcard := Finset.card_le_card hsub
        rw [Nat.card_Ico, ← hkdef] at hcard
        omega
      calc k * (k + 1) = (k + 1) * k := mul_comm _ _
        _ ≤ (k + 2 + p₁) * (pK - 1) :=
          mul_le_mul hk1 hk2' (Nat.zero_le _) (Nat.zero_le _)
    refine ⟨p₀, hp₀, ?_⟩
    rw [← hMdef]
    exact lt_of_lt_of_le hMltK hKle

/-- **Dichotomy for odd primitive non-deficient numbers.** Let $n$ be an odd primitive
non-deficient number, that is, a positive integer with $\sigma(n) \ge 2n$ all of whose proper
divisors $m$ satisfy $\sigma(m) < 2m$, where $\sigma$ is the sum of divisors. Let $k$ be the
number of distinct prime factors of $n$, let $p_1$ and $p_k$ be its least and greatest prime
factors, and let $R$ be the product of the distinct primes dividing $n$. Then either
$p_k < \sqrt{R}$, or some prime $p$ dividing $n$ satisfies $p^{a+1} < (k + 2 + p_1)(p_k - 1)$,
where $a$ is the exponent of $p$ in $n$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Proposition
(label `dichotomywithpk`). -/
theorem max_primeFactor_lt_sqrt_radical_or_exists_pow_lt
    (n p₁ pK : ℕ) (hno : Odd n)
    (hn : IsPrimitiveNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors)
    (hmin : ∀ q ∈ n.primeFactors, p₁ ≤ q)
    (hpK : pK ∈ n.primeFactors)
    (hmax : ∀ q ∈ n.primeFactors, q ≤ pK) :
    (pK : ℝ) < Real.sqrt ((∏ q ∈ n.primeFactors, q : ℕ) : ℝ) ∨
      ∃ p ∈ n.primeFactors,
        p ^ (n.factorization p + 1) <
          (n.primeFactors.card + 2 + p₁) * (pK - 1) := by
  by_cases hsqrt : (pK : ℝ) < Real.sqrt ((∏ q ∈ n.primeFactors, q : ℕ) : ℝ)
  · exact Or.inl hsqrt
  · right
    have hnsqrt : Real.sqrt ((∏ q ∈ n.primeFactors, q : ℕ) : ℝ) ≤ (pK : ℝ) :=
      le_of_not_gt hsqrt
    have hlt := radical_gt_two_mul_phi n p₁ hn.1 hp₁
    have hH2 := abundancySup_gt_two n p₁ hn.1 hp₁
    have hbig : 2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1)
        ≤ (∏ q ∈ n.primeFactors, q) - 2 * ∏ p ∈ n.primeFactors, (p - 1) := by
      by_contra hcon
      have hlt' : (∏ q ∈ n.primeFactors, q) - 2 * ∏ p ∈ n.primeFactors, (p - 1)
          < 2 * ∏ p ∈ n.primeFactors.erase pK, (p - 1) := not_le.mp hcon
      have hsqrt' := max_prime_lt_sqrt_of_excess_lt n pK hpK hlt hlt' hH2
      linarith [hnsqrt, hsqrt']
    exact exists_small_component n p₁ pK hno hn hp₁ hmin hpK hmax hbig

end MathlibExt.NumberTheory.PrimitiveNondeficientWanted
