/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SquareSplittingConvolution
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.PrimeFin
import MathlibExt.NumberTheory.SquareSplittingConvolution.DivisorProperties
import MathlibExt.NumberTheory.ArithmeticFunction.JordanTotient
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.Divisors

/-!
# The square-splitting totient function

The integer-valued arithmetic function summing to the identity over
square-splitting divisors is multiplicative, with the stated prime-power values
and Euler-totient product formula.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 7.
-/

namespace MetaMathlibExt

-- The value at `1`: the only square-splitting divisor of `1` is `1`.
private theorem phi_one (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) : φ 1 = 1 := by
  have h := hφ 1 one_ne_zero
  rw [squareSplitDivisors_one, Finset.sum_singleton] at h
  simpa using h

-- The squarefree part of a prime power.
private theorem squareSplitU_prime_pow (p k : ℕ) (hp : p.Prime) :
    squareSplitU (p ^ k) = p ^ (k % 2) := by
  unfold squareSplitU
  rw [hp.factorization_pow, Finsupp.prod_single_index (by simp)]

-- The square-root part of a prime power.
private theorem squareSplitV_prime_pow (p k : ℕ) (hp : p.Prime) :
    squareSplitV (p ^ k) = p ^ (k / 2) := by
  unfold squareSplitV
  rw [hp.factorization_pow, Finsupp.prod_single_index (by simp)]

-- Membership in the square-splitting divisor set of a prime power.
private theorem mem_squareSplitDivisors_prime_pow (p k d : ℕ) (hp : p.Prime) :
    d ∈ squareSplitDivisors (p ^ k) ↔
      (∃ j ≤ k / 2, d = p ^ (2 * j)) ∨ (Odd k ∧ ∃ j ≤ k / 2, d = p ^ (2 * j + 1)) := by
  rw [squareSplitDivisors, squareSplitU_prime_pow _ _ hp, squareSplitV_prime_pow _ _ hp]
  constructor
  · intro h
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    obtain ⟨e, he, rfl⟩ := (Nat.mem_divisors_prime_pow hp (k % 2)).mp hu
    obtain ⟨j, hj, rfl⟩ := (Nat.mem_divisors_prime_pow hp (k / 2)).mp hv
    have hmod : k % 2 < 2 := by omega
    have he2 : e = 0 ∨ e = 1 := by omega
    have hsq : (p ^ j) ^ 2 = p ^ (2 * j) := by rw [← pow_mul, mul_comm]
    rcases he2 with rfl | rfl
    · exact Or.inl ⟨j, hj, by change p ^ 0 * (p ^ j) ^ 2 = _; rw [pow_zero, one_mul, hsq]⟩
    · have hmod1 : k % 2 = 1 := by omega
      have hodd : Odd k := ⟨k / 2, by omega⟩
      exact Or.inr ⟨hodd, j, hj,
        by change p ^ 1 * (p ^ j) ^ 2 = _; rw [pow_one, hsq, pow_succ', mul_comm p (p ^ (2 * j))]⟩
  · intro h
    have hsq : ∀ j, (p ^ j) ^ 2 = p ^ (2 * j) := fun j => by rw [← pow_mul, mul_comm]
    rcases h with ⟨j, hj, rfl⟩ | ⟨hodd, j, hj, rfl⟩
    · have h1mem : 1 ∈ (p ^ (k % 2)).divisors :=
        (Nat.mem_divisors_prime_pow hp (k % 2)).mpr ⟨0, Nat.zero_le _, (pow_zero p).symm⟩
      have hjmem : p ^ j ∈ (p ^ (k / 2)).divisors :=
        (Nat.mem_divisors_prime_pow hp (k / 2)).mpr ⟨j, hj, rfl⟩
      exact Finset.mem_image.mpr ⟨(1, p ^ j), Finset.mem_product.mpr ⟨h1mem, hjmem⟩,
        by change 1 * (p ^ j) ^ 2 = _; rw [one_mul, hsq]⟩
    · obtain ⟨m, hm⟩ := hodd
      have hk1 : k % 2 = 1 := by omega
      have hpmem : p ∈ (p ^ (k % 2)).divisors := by
        rw [hk1]
        exact (Nat.mem_divisors_prime_pow hp 1).mpr ⟨1, le_rfl, (pow_one p).symm⟩
      have hjmem : p ^ j ∈ (p ^ (k / 2)).divisors :=
        (Nat.mem_divisors_prime_pow hp (k / 2)).mpr ⟨j, hj, rfl⟩
      exact Finset.mem_image.mpr ⟨(p, p ^ j), Finset.mem_product.mpr ⟨hpmem, hjmem⟩,
        by change p * (p ^ j) ^ 2 = _; rw [hsq, pow_succ', mul_comm p (p ^ (2 * j))]⟩

-- The square-splitting divisors of an even prime power.
private theorem squareSplitDivisors_prime_pow_even (p b : ℕ) (hp : p.Prime) :
    squareSplitDivisors (p ^ (2 * b)) =
      (Finset.range (b + 1)).image fun j => p ^ (2 * j) := by
  ext d
  rw [mem_squareSplitDivisors_prime_pow _ _ _ hp]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · intro h
    cases h with
    | inl h =>
      obtain ⟨j, hj, rfl⟩ := h
      exact ⟨j, by omega, rfl⟩
    | inr h =>
      obtain ⟨hodd, _⟩ := h
      obtain ⟨m, hm⟩ := hodd
      omega
  · intro h
    obtain ⟨j, hj, rfl⟩ := h
    exact Or.inl ⟨j, by omega, rfl⟩

-- The square-splitting divisors of an odd prime power.
private theorem squareSplitDivisors_prime_pow_odd (p b : ℕ) (hp : p.Prime) :
    squareSplitDivisors (p ^ (2 * b + 1)) =
      ((Finset.range (b + 1)).image fun j => p ^ (2 * j)) ∪
        ((Finset.range (b + 1)).image fun j => p ^ (2 * j + 1)) := by
  ext d
  rw [mem_squareSplitDivisors_prime_pow _ _ _ hp]
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_union]
  constructor
  · intro h
    cases h with
    | inl h =>
      obtain ⟨j, hj, rfl⟩ := h
      exact Or.inl ⟨j, by omega, rfl⟩
    | inr h =>
      obtain ⟨_, j, hj, rfl⟩ := h
      exact Or.inr ⟨j, by omega, rfl⟩
  · intro h
    cases h with
    | inl h =>
      obtain ⟨j, hj, rfl⟩ := h
      exact Or.inl ⟨j, by omega, rfl⟩
    | inr h =>
      obtain ⟨j, hj, rfl⟩ := h
      exact Or.inr ⟨⟨b, rfl⟩, j, by omega, rfl⟩

-- Powers `p ^ (2 * j)` are injective in `j` for prime `p`.
private theorem inj_pow_two_mul (p : ℕ) (hp : p.Prime) :
    Function.Injective fun j => p ^ (2 * j) := by
  intro a b hab
  have h := Nat.pow_right_injective hp.two_le hab
  omega

-- Powers `p ^ (2 * j + 1)` are injective in `j` for prime `p`.
private theorem inj_pow_two_mul_succ (p : ℕ) (hp : p.Prime) :
    Function.Injective fun j => p ^ (2 * j + 1) := by
  intro a b hab
  have h := Nat.pow_right_injective hp.two_le hab
  omega

-- Even and odd prime powers are disjoint.
private theorem disjoint_pow_even_odd (p b : ℕ) (hp : p.Prime) :
    Disjoint ((Finset.range (b + 1)).image fun j => p ^ (2 * j))
      ((Finset.range (b + 1)).image fun j => p ^ (2 * j + 1)) := by
  rw [Finset.disjoint_left]
  intro d hd1 hd2
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd1
  obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp hd2
  have h := Nat.pow_right_injective hp.two_le hj'
  omega

-- The divisor sum over even prime powers.
private theorem sum_range_even (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (p b : ℕ) (hp : p.Prime) :
    ∑ j ∈ Finset.range (b + 1), φ (p ^ (2 * j)) = (p : ℤ) ^ (2 * b) := by
  have h := hφ (p ^ (2 * b)) (pow_ne_zero _ hp.pos.ne')
  rw [squareSplitDivisors_prime_pow_even _ _ hp,
    Finset.sum_image (fun x _ y _ hxy => inj_pow_two_mul p hp hxy)] at h
  rw [Nat.cast_pow] at h
  exact h

-- The divisor sum over an even and odd prime-power pair.
private theorem sum_range_odd (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (p b : ℕ) (hp : p.Prime) :
    ∑ j ∈ Finset.range (b + 1), (φ (p ^ (2 * j)) + φ (p ^ (2 * j + 1))) =
      (p : ℤ) ^ (2 * b + 1) := by
  have h := hφ (p ^ (2 * b + 1)) (pow_ne_zero _ hp.pos.ne')
  rw [squareSplitDivisors_prime_pow_odd _ _ hp,
    Finset.sum_union (disjoint_pow_even_odd _ _ hp),
    Finset.sum_image (fun x _ y _ hxy => inj_pow_two_mul p hp hxy),
    Finset.sum_image (fun x _ y _ hxy => inj_pow_two_mul_succ p hp hxy),
    ← Finset.sum_add_distrib, Nat.cast_pow] at h
  exact h

-- The value at a prime.
private theorem phi_prime (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (p : ℕ) (hp : p.Prime) :
    φ p = (p : ℤ) - 1 := by
  have h1 := phi_one φ hφ
  have h := sum_range_odd φ hφ p 0 hp
  rw [Finset.sum_range_one] at h
  simp only [mul_zero, zero_add, pow_zero, pow_one] at h
  rw [h1] at h
  omega

-- The value at an even prime power.
private theorem phi_prime_pow_even (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (p b : ℕ) (hp : p.Prime)
    (hb : 1 ≤ b) :
    φ (p ^ (2 * b)) = ((p : ℤ) ^ 2 - 1) * (p : ℤ) ^ (2 * b - 2) := by
  have hE1 := sum_range_even φ hφ p b hp
  have hE0 := sum_range_even φ hφ p (b - 1) hp
  have hexp : 2 * (b - 1) = 2 * b - 2 := by omega
  rw [Nat.sub_add_cancel hb, hexp] at hE0
  rw [Finset.sum_range_succ] at hE1
  have hpow : (p : ℤ) ^ (2 * b) = (p : ℤ) ^ (2 * b - 2) * (p : ℤ) ^ 2 := by
    conv_lhs => rw [show 2 * b = (2 * b - 2) + 2 from by omega]
    rw [pow_add]
  have hval : φ (p ^ (2 * b)) = (p : ℤ) ^ (2 * b) - (p : ℤ) ^ (2 * b - 2) := by omega
  rw [hval, hpow]
  ring

-- The value at an odd prime power beyond the prime itself.
private theorem phi_prime_pow_odd (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (p b : ℕ) (hp : p.Prime)
    (hb : 1 ≤ b) :
    φ (p ^ (2 * b + 1)) = ((p : ℤ) - 1) * ((p : ℤ) ^ 2 - 1) * (p : ℤ) ^ (2 * b - 2) := by
  have hO1 := sum_range_odd φ hφ p b hp
  have hO0 := sum_range_odd φ hφ p (b - 1) hp
  have hexp : 2 * (b - 1) + 1 = 2 * b - 1 := by omega
  rw [Nat.sub_add_cancel hb, hexp] at hO0
  rw [Finset.sum_range_succ] at hO1
  have hE := phi_prime_pow_even φ hφ p b hp hb
  have hval : φ (p ^ (2 * b + 1))
      = (p : ℤ) ^ (2 * b + 1) - (p : ℤ) ^ (2 * b - 1)
        - (((p : ℤ) ^ 2 - 1) * (p : ℤ) ^ (2 * b - 2)) := by
    omega
  have hpow1 : (p : ℤ) ^ (2 * b + 1) = (p : ℤ) ^ (2 * b - 2) * (p : ℤ) ^ 3 := by
    conv_lhs => rw [show 2 * b + 1 = (2 * b - 2) + 3 from by omega]
    rw [pow_add]
  have hpow0 : (p : ℤ) ^ (2 * b - 1) = (p : ℤ) ^ (2 * b - 2) * (p : ℤ) := by
    conv_lhs => rw [show 2 * b - 1 = (2 * b - 2) + 1 from by omega]
    rw [pow_add, pow_one]
  rw [hval, hpow1, hpow0]
  ring

-- The squarefree part divides the number.
private theorem squareSplitU_dvd (n : ℕ) (hn : n ≠ 0) : squareSplitU n ∣ n :=
  ⟨squareSplitV n ^ 2, (squareSplitU_mul_squareSplitV_sq hn).symm⟩

-- The square-root part divides the number.
private theorem squareSplitV_dvd (n : ℕ) (hn : n ≠ 0) : squareSplitV n ∣ n := by
  refine ⟨squareSplitU n * squareSplitV n, ?_⟩
  conv_lhs => rw [← squareSplitU_mul_squareSplitV_sq hn]
  ring

-- The squarefree part is multiplicative on coprime inputs.
private theorem squareSplitU_mul_of_coprime (m n : ℕ) (h : m.Coprime n) :
    squareSplitU (m * n) = squareSplitU m * squareSplitU n := by
  unfold squareSplitU
  rw [Nat.factorization_mul_of_coprime h]
  exact Finsupp.prod_add_index_of_disjoint h.disjoint_primeFactors _

-- The square-root part is multiplicative on coprime inputs.
private theorem squareSplitV_mul_of_coprime (m n : ℕ) (h : m.Coprime n) :
    squareSplitV (m * n) = squareSplitV m * squareSplitV n := by
  unfold squareSplitV
  rw [Nat.factorization_mul_of_coprime h]
  exact Finsupp.prod_add_index_of_disjoint h.disjoint_primeFactors _

-- Any `φ` satisfying the divisor-sum equation is multiplicative on coprime inputs.
private theorem phi_mul_of_coprime (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) {m n : ℕ}
    (h : m.Coprime n) : φ (m * n) = φ m * φ n := by
  suffices H : ∀ N m n : ℕ, m * n = N → m.Coprime n → φ (m * n) = φ m * φ n from
    H _ _ _ rfl h
  intro N
  refine Nat.strong_induction_on N ?_
  intro N IH m n hN hcop
  by_cases hmn0 : m * n = 0
  · rw [hmn0]
    cases Nat.mul_eq_zero.mp hmn0 with
    | inl hm =>
      rw [hm, ArithmeticFunction.map_zero, zero_mul]
    | inr hn =>
      rw [hn, ArithmeticFunction.map_zero, mul_zero]
  · have hm : m ≠ 0 := fun h => hmn0 (by rw [h, zero_mul])
    have hn : n ≠ 0 := fun h => hmn0 (by rw [h, mul_zero])
    obtain ⟨hmem, hmul, _⟩ := squareSplitDivisors_properties
    have hmem_m := hmem m hm
    have hmem_n := hmem n hn
    have hφm := hφ m hm
    have hφn := hφ n hn
    have hsubM : squareSplitDivisors m ⊆ m.divisors := fun d hd =>
      Nat.mem_divisors.mpr ⟨hmem_m.2.2 d hd, hm⟩
    have hsubN : squareSplitDivisors n ⊆ n.divisors := fun d hd =>
      Nat.mem_divisors.mpr ⟨hmem_n.2.2 d hd, hn⟩
    have hsub := Finset.product_subset_product hsubM hsubN
    have hinj : ∀ x ∈ squareSplitDivisors m ×ˢ squareSplitDivisors n,
        ∀ y ∈ squareSplitDivisors m ×ˢ squareSplitDivisors n,
          x.1 * x.2 = y.1 * y.2 → x = y := by
      intro x hx y hy hxy
      exact Nat.Coprime.mul_injOn_divisors hcop (hsub hx) (hsub hy) hxy
    have hφmn : ∑ x ∈ squareSplitDivisors m ×ˢ squareSplitDivisors n, φ (x.1 * x.2)
        = ((m * n : ℕ) : ℤ) := by
      have h := hφ (m * n) hmn0
      rw [hmul m n hcop, Finset.sum_image hinj] at h
      exact h
    have hmem_prod : (m, n) ∈ squareSplitDivisors m ×ˢ squareSplitDivisors n :=
      Finset.mem_product.mpr ⟨hmem_m.2.1, hmem_n.2.1⟩
    have hsplit := Finset.add_sum_erase _ (fun x : ℕ × ℕ => φ (x.1 * x.2)) hmem_prod
    have hsplit2 := Finset.add_sum_erase _ (fun x : ℕ × ℕ => φ x.1 * φ x.2) hmem_prod
    have hEq : ∑ x ∈ (squareSplitDivisors m ×ˢ squareSplitDivisors n).erase (m, n),
          φ (x.1 * x.2)
        = ∑ x ∈ (squareSplitDivisors m ×ˢ squareSplitDivisors n).erase (m, n),
          φ x.1 * φ x.2 := by
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨a, b⟩ := x
      have hne : (a, b) ≠ (m, n) := Finset.ne_of_mem_erase hx
      have hmemab : (a, b) ∈ squareSplitDivisors m ×ˢ squareSplitDivisors n :=
        Finset.mem_of_mem_erase hx
      obtain ⟨ham, hbn⟩ := Finset.mem_product.mp hmemab
      have hdvd_a : a ∣ m := hmem_m.2.2 a ham
      have hdvd_b : b ∣ n := hmem_n.2.2 b hbn
      have hle_a : a ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd_a
      have hle_b : b ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd_b
      have hlt : a * b < m * n := by
        by_cases ha : a = m
        · by_cases hb : b = n
          · exfalso
            exact hne (by rw [ha, hb])
          · exact Nat.mul_lt_mul_of_le_of_lt hle_a (lt_of_le_of_ne hle_b hb)
              (Nat.pos_of_ne_zero hm)
        · exact Nat.mul_lt_mul_of_lt_of_le (lt_of_le_of_ne hle_a ha) hle_b
            (Nat.pos_of_ne_zero hn)
      have hltN : a * b < N := by rw [← hN]; exact hlt
      have hcop_ab : a.Coprime b :=
        Nat.Coprime.coprime_dvd_right hdvd_b (Nat.Coprime.coprime_dvd_left hdvd_a hcop)
      exact IH (a * b) hltN a b rfl hcop_ab
    have hsumprod : ∑ x ∈ squareSplitDivisors m ×ˢ squareSplitDivisors n, φ x.1 * φ x.2
        = (m : ℤ) * (n : ℤ) := by
      rw [← hφm, ← hφn, Finset.sum_mul_sum, Finset.sum_product]
    have hcast : ((m * n : ℕ) : ℤ) = (m : ℤ) * (n : ℤ) := Nat.cast_mul _ _
    have e1 : φ (m * n)
          + ∑ x ∈ (squareSplitDivisors m ×ˢ squareSplitDivisors n).erase (m, n),
            φ (x.1 * x.2)
        = ∑ x ∈ squareSplitDivisors m ×ˢ squareSplitDivisors n, φ (x.1 * x.2) := hsplit
    have e2 : φ m * φ n
          + ∑ x ∈ (squareSplitDivisors m ×ˢ squareSplitDivisors n).erase (m, n),
            φ x.1 * φ x.2
        = ∑ x ∈ squareSplitDivisors m ×ˢ squareSplitDivisors n, φ x.1 * φ x.2 := hsplit2
    omega

-- Any `φ` satisfying the divisor-sum equation is multiplicative.
private theorem phi_isMultiplicative (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) : φ.IsMultiplicative :=
  ⟨phi_one φ hφ, phi_mul_of_coprime φ hφ⟩

-- The totient-product formula as a rational-valued arithmetic function.
private def rhsFun : ArithmeticFunction ℚ :=
  ⟨fun n => if n = 0 then 0 else (squareSplitU n).totient * (squareSplitV n : ℚ) ^ 2 *
    ∏ p ∈ (squareSplitV n).primeFactors, (1 - 1 / (p : ℚ) ^ 2), by simp⟩

private theorem rhsFun_apply (n : ℕ) : rhsFun n =
    (if n = 0 then (0 : ℚ) else (squareSplitU n).totient * (squareSplitV n : ℚ) ^ 2 *
      ∏ p ∈ (squareSplitV n).primeFactors, (1 - 1 / (p : ℚ) ^ 2)) := rfl

private theorem rhsFun_zero : rhsFun 0 = 0 := rfl

private theorem rhsFun_one : rhsFun 1 = 1 := by
  rw [rhsFun_apply, ite_eq_right one_ne_zero]
  simp [squareSplitU_one, squareSplitV_one, Nat.totient_one]

private theorem rhsFun_mul {m n : ℕ} (h : m.Coprime n) :
    rhsFun (m * n) = rhsFun m * rhsFun n := by
  by_cases hmn0 : m * n = 0
  · rw [hmn0, rhsFun_zero]
    cases Nat.mul_eq_zero.mp hmn0 with
    | inl hm =>
      rw [hm, rhsFun_zero, zero_mul]
    | inr hn =>
      rw [hn, rhsFun_zero, mul_zero]
  · have hm : m ≠ 0 := fun h => hmn0 (by rw [h, zero_mul])
    have hn : n ≠ 0 := fun h => hmn0 (by rw [h, mul_zero])
    have hU := squareSplitU_mul_of_coprime m n h
    have hV := squareSplitV_mul_of_coprime m n h
    have hu_cop : (squareSplitU m).Coprime (squareSplitU n) :=
      Nat.Coprime.coprime_dvd_right (squareSplitU_dvd n hn)
        (Nat.Coprime.coprime_dvd_left (squareSplitU_dvd m hm) h)
    have hv_cop : (squareSplitV m).Coprime (squareSplitV n) :=
      Nat.Coprime.coprime_dvd_right (squareSplitV_dvd n hn)
        (Nat.Coprime.coprime_dvd_left (squareSplitV_dvd m hm) h)
    rw [rhsFun_apply, rhsFun_apply, rhsFun_apply, ite_eq_right hmn0, ite_eq_right hm,
      ite_eq_right hn, hU, hV,
      Nat.totient_mul hu_cop, Nat.Coprime.primeFactors_mul hv_cop,
      Finset.prod_union hv_cop.disjoint_primeFactors]
    simp only [Nat.cast_mul, mul_pow]
    ring

private theorem rhsFun_isMultiplicative : rhsFun.IsMultiplicative :=
  ⟨rhsFun_one, rhsFun_mul⟩

-- The square-part factor at a prime power.
private theorem psi_prime_pow (p b : ℕ) (hp : p.Prime) (hb : 1 ≤ b) :
    ((p ^ b : ℕ) : ℚ) ^ 2 * ∏ q ∈ (p ^ b).primeFactors, (1 - 1 / (q : ℚ) ^ 2)
      = ((p : ℚ) ^ 2 - 1) * (p : ℚ) ^ (2 * b - 2) := by
  rw [← ArithmeticFunction.jordanTotient_eq_rational_prod (pow_ne_zero _ hp.ne_zero),
    ArithmeticFunction.jordanTotient_prime_pow hp (by omega),
    show 2 * (b - 1) = 2 * b - 2 by omega, Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ hp.pos),
    Nat.cast_pow, Nat.cast_pow, Nat.cast_one, mul_comm]

-- Agreement on even prime powers.
private theorem agree_even (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (p b : ℕ) (hp : p.Prime)
    (hb : 1 ≤ b) : (φ : ArithmeticFunction ℚ) (p ^ (2 * b)) = rhsFun (p ^ (2 * b)) := by
  rw [ArithmeticFunction.intCoe_apply, rhsFun_apply, ite_eq_right (pow_ne_zero _ hp.pos.ne')]
  rw [phi_prime_pow_even φ hφ p b hp hb]
  have hm2 : (2 * b) % 2 = 0 := by omega
  have hd2 : (2 * b) / 2 = b := by omega
  rw [squareSplitU_prime_pow _ _ hp, squareSplitV_prime_pow _ _ hp, hm2, hd2, pow_zero,
    Nat.totient_one, Nat.cast_one, one_mul, psi_prime_pow p b hp hb]
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_one, Int.cast_natCast]

-- Agreement on odd prime powers.
private theorem agree_odd (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (p b : ℕ) (hp : p.Prime) :
    (φ : ArithmeticFunction ℚ) (p ^ (2 * b + 1)) = rhsFun (p ^ (2 * b + 1)) := by
  rw [ArithmeticFunction.intCoe_apply, rhsFun_apply, ite_eq_right (pow_ne_zero _ hp.pos.ne')]
  have hm2 : (2 * b + 1) % 2 = 1 := by omega
  have hd2 : (2 * b + 1) / 2 = b := by omega
  rw [squareSplitU_prime_pow _ _ hp, squareSplitV_prime_pow _ _ hp, hm2, hd2, pow_one,
    Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le]
  by_cases hb : b = 0
  · subst hb
    simp only [mul_zero, zero_add, pow_one]
    rw [phi_prime φ hφ p hp, pow_zero, Nat.primeFactors_one, Finset.prod_empty, Int.cast_sub,
      Int.cast_natCast, Int.cast_one, Nat.cast_one, one_pow, mul_one, mul_one]
  · have hb1 : 1 ≤ b := by omega
    rw [phi_prime_pow_odd φ hφ p b hp hb1, Nat.cast_one]
    have hfactor : ((p : ℚ) - 1) * (((p ^ b : ℕ) : ℚ) ^ 2)
          * ∏ q ∈ (p ^ b).primeFactors, (1 - 1 / (q : ℚ) ^ 2)
        = ((p : ℚ) - 1) * (((p : ℚ) ^ 2 - 1) * (p : ℚ) ^ (2 * b - 2)) := by
      rw [mul_assoc, psi_prime_pow p b hp hb1]
    rw [hfactor]
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_one, Int.cast_natCast]
    ring

-- Agreement on all prime powers.
private theorem agree_prime_pow (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (p i : ℕ) (hp : p.Prime) :
    (φ : ArithmeticFunction ℚ) (p ^ i) = rhsFun (p ^ i) := by
  cases i with
  | zero =>
    rw [pow_zero, ((phi_isMultiplicative φ hφ).intCast (R := ℚ)).1, rhsFun_one]
  | succ i =>
    have hmod : (i + 1) % 2 = 0 ∨ (i + 1) % 2 = 1 := by omega
    cases hmod with
    | inl h0 =>
      have heven : Even (i + 1) := ⟨(i + 1) / 2, by omega⟩
      obtain ⟨b, hb⟩ := heven
      have hb1 : 1 ≤ b := by omega
      rw [hb, ← two_mul]
      exact agree_even φ hφ p b hp hb1
    | inr h1 =>
      have hodd : Odd (i + 1) := ⟨(i + 1) / 2, by omega⟩
      obtain ⟨b, hb⟩ := hodd
      rw [hb]
      exact agree_odd φ hφ p b hp

/-- **The square-splitting totient function.** Let $A(n)$ be the set of square-splitting divisors
of $n$, and let $\varphi_\star$ be any integer-valued arithmetic function with
$\sum_{d \in A(n)} \varphi_\star(d) = n$ for every $n \ge 1$. Then $\varphi_\star$ is
multiplicative and $\varphi_\star(1) = 1$. For every prime $p$, $\varphi_\star(p) = p - 1$, and
for every $b \ge 1$, $\varphi_\star(p^{2b}) = (p^2 - 1)\,p^{2b-2}$ and
$\varphi_\star(p^{2b+1}) = (p - 1)(p^2 - 1)\,p^{2b-2}$. Moreover, for every $n \ge 1$,
$$\varphi_\star(n) = \varphi(u(n))\,v(n)^2 \prod_{p \mid v(n)} \left(1 - \frac{1}{p^2}\right),$$
where $\varphi$ is Euler's totient function, $u(n)$ is the product of the primes dividing $n$ to
an odd power and $v(n)$ is the positive integer with $n = u(n)\,v(n)^2$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 7
(`integers-2026-A56-thm-7`). -/
public theorem squareSplitTotient_formula (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) :
    φ.IsMultiplicative ∧ φ 1 = 1 ∧
    (∀ p : ℕ, p.Prime → φ p = (p : ℤ) - 1 ∧
      ∀ b, 1 ≤ b → φ (p ^ (2 * b)) = ((p : ℤ) ^ 2 - 1) * (p : ℤ) ^ (2 * b - 2) ∧
        φ (p ^ (2 * b + 1)) = ((p : ℤ) - 1) * ((p : ℤ) ^ 2 - 1) * (p : ℤ) ^ (2 * b - 2)) ∧
    ∀ n ≠ 0, (φ n : ℚ) = (squareSplitU n).totient * (squareSplitV n : ℚ) ^ 2 *
      ∏ p ∈ (squareSplitV n).primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  refine ⟨phi_isMultiplicative φ hφ, phi_one φ hφ, ?_, ?_⟩
  · intro p hp
    exact ⟨phi_prime φ hφ p hp, fun b hb => ⟨phi_prime_pow_even φ hφ p b hp hb,
      phi_prime_pow_odd φ hφ p b hp hb⟩⟩
  · intro n hn
    have hFG : (φ : ArithmeticFunction ℚ) = rhsFun :=
      (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers (φ : ArithmeticFunction ℚ)
        (phi_isMultiplicative φ hφ).intCast rhsFun rhsFun_isMultiplicative).mpr
        (agree_prime_pow φ hφ)
    have hnod : (φ : ArithmeticFunction ℚ) n = rhsFun n := by rw [hFG]
    rw [ArithmeticFunction.intCoe_apply, rhsFun_apply, ite_eq_right hn] at hnod
    exact hnod

end MetaMathlibExt
