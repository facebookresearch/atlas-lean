/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SquareSplittingConvolution
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import MathlibExt.NumberTheory.SquareSplittingConvolution.DivisorProperties
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.LinearCombination

/-!
# Inverse of a multiplicative function under the square-splitting convolution

A multiplicative complex arithmetic function has a unique inverse under the
square-splitting convolution; the inverse is multiplicative with explicit
prime-power values.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 5.
-/

namespace MetaMathlibExt

@[expose] public section

private noncomputable def squareSplitInvFun (f : ArithmeticFunction ℂ) (n : ℕ) : ℂ :=
  if hn0 : n = 0 then 0
  else if hn1 : n = 1 then (f 1)⁻¹
  else -(f 1)⁻¹ * ∑ d : (squareSplitDivisors n).erase 1,
    have : n / (d : ℕ) < n := by
      obtain ⟨hdne, hdmem⟩ := Finset.mem_erase.mp d.2
      have hdiv : (d : ℕ) ∣ n :=
        (squareSplitDivisors_properties.1 n hn0).2.2 _ hdmem
      have hd0 : (d : ℕ) ≠ 0 := by
        rintro h0
        rw [h0] at hdiv
        simp at hdiv
        exact hn0 hdiv
      have hd1 : 1 < (d : ℕ) := by omega
      exact Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hd1
    f d * squareSplitInvFun f (n / d)

private theorem squareSplitInvFun_apply_zero (f : ArithmeticFunction ℂ) :
    squareSplitInvFun f 0 = 0 := by
  rw [squareSplitInvFun, dite_eq_left rfl]

private theorem squareSplitInvFun_apply_one (f : ArithmeticFunction ℂ) :
    squareSplitInvFun f 1 = (f 1)⁻¹ := by
  rw [squareSplitInvFun, dite_eq_right one_ne_zero, dite_eq_left rfl]

private theorem squareSplitInvFun_apply_ne (f : ArithmeticFunction ℂ) {n : ℕ} (hn0 : n ≠ 0)
    (hn1 : n ≠ 1) :
    squareSplitInvFun f n =
      -(f 1)⁻¹ * ∑ d ∈ (squareSplitDivisors n).erase 1, f d * squareSplitInvFun f (n / d) := by
  rw [squareSplitInvFun, dite_eq_right hn0, dite_eq_right hn1]
  conv_rhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]

private noncomputable def squareSplitInv (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨squareSplitInvFun f, squareSplitInvFun_apply_zero f⟩

private theorem squareSplitInv_apply (f : ArithmeticFunction ℂ) (n : ℕ) :
    squareSplitInv f n = squareSplitInvFun f n := rfl

private theorem squareSplitConv_squareSplitInv (f : ArithmeticFunction ℂ) (hf1 : f 1 ≠ 0) :
    squareSplitConv f (squareSplitInv f) = 1 := by
  ext n
  by_cases hn0 : n = 0
  · simp [hn0]
  · by_cases hn1 : n = 1
    · subst hn1
      rw [squareSplitConv_apply _ _ one_ne_zero, squareSplitDivisors_one]
      simp [squareSplitInv_apply, squareSplitInvFun_apply_one, mul_inv_cancel₀ hf1]
    · rw [squareSplitConv_apply _ _ hn0, ArithmeticFunction.one_apply_ne hn1]
      have h1mem : 1 ∈ squareSplitDivisors n := (squareSplitDivisors_properties.1 n hn0).1
      rw [← Finset.add_sum_erase _ _ h1mem, Nat.div_one]
      simp only [squareSplitInv_apply]
      rw [squareSplitInvFun_apply_ne _ hn0 hn1]
      have hcancel : f 1 * (-(f 1)⁻¹ * ∑ d ∈ (squareSplitDivisors n).erase 1,
        f d * squareSplitInvFun f (n / d)) =
        -∑ d ∈ (squareSplitDivisors n).erase 1, f d * squareSplitInvFun f (n / d) := by
        rw [neg_mul, mul_neg, ← mul_assoc, mul_inv_cancel₀ hf1, one_mul]
      rw [hcancel, neg_add_cancel]

private theorem squareSplitConv_right_unique (f g g' : ArithmeticFunction ℂ)
    (hf1 : f 1 ≠ 0) (hfg : squareSplitConv f g = 1)
    (hfg' : squareSplitConv f g' = 1) : g' = g := by
  have key : ∀ n, g' n = g n := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n IH =>
      by_cases hn0 : n = 0
      · subst hn0
        simp only [ArithmeticFunction.map_zero]
      · have e1 := DFunLike.congr_fun hfg' n
        have e2 := DFunLike.congr_fun hfg n
        rw [squareSplitConv_apply _ _ hn0] at e1 e2
        have h1mem : 1 ∈ squareSplitDivisors n := (squareSplitDivisors_properties.1 n hn0).1
        rw [← Finset.add_sum_erase _ _ h1mem, Nat.div_one] at e1 e2
        have herase : ∑ d ∈ (squareSplitDivisors n).erase 1, f d * g' (n / d) =
            ∑ d ∈ (squareSplitDivisors n).erase 1, f d * g (n / d) := by
          apply Finset.sum_congr rfl
          intro d hd
          obtain ⟨hdne, hdmem⟩ := Finset.mem_erase.mp hd
          have hdiv : d ∣ n := (squareSplitDivisors_properties.1 n hn0).2.2 _ hdmem
          have hd0 : d ≠ 0 := by
            rintro h0
            rw [h0] at hdiv
            simp at hdiv
            exact hn0 hdiv
          have hlt : n / d < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by omega)
          rw [IH _ hlt]
        rw [herase] at e1
        have hmul : f 1 * g' n = f 1 * g n := add_right_cancel (e1.trans e2.symm)
        exact mul_left_cancel₀ hf1 hmul
  ext n
  exact key n

private theorem one_lt_mul_of_ne_one_one {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hne : (a, b) ≠ (1, 1)) : 1 < a * b := by
  by_contra hcon
  rw [not_lt] at hcon
  have hge : 1 ≤ a * b := by
    calc (1:ℕ) = 1 * 1 := (mul_one 1).symm
    _ ≤ a * b := Nat.mul_le_mul ha hb
  have heq : a * b = 1 := Nat.le_antisymm hcon hge
  have ha1 : a = 1 := Nat.dvd_one.mp ⟨b, heq.symm⟩
  have hb1 : b = 1 := Nat.dvd_one.mp ⟨a, by rw [mul_comm b a]; exact heq.symm⟩
  exact hne (Prod.ext ha1 hb1)

private theorem squareSplitInv_isMultiplicative {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) : (squareSplitInv f).IsMultiplicative := by
  have hf1 : f 1 = 1 := hf.1
  have hg1 : squareSplitInv f 1 = 1 := by
    rw [squareSplitInv_apply, squareSplitInvFun_apply_one, hf1, inv_one]
  have hf1ne : f 1 ≠ 0 := by rw [hf1]; exact one_ne_zero
  have hfg : squareSplitConv f (squareSplitInv f) = 1 :=
    squareSplitConv_squareSplitInv f hf1ne
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨hg1, ?_⟩
  intro m n hm hn hcop
  have key : ∀ N m n : ℕ, m ≠ 0 → n ≠ 0 → m.Coprime n → m * n < N →
      squareSplitInv f (m * n) = squareSplitInv f m * squareSplitInv f n := by
    intro N
    induction N using Nat.strong_induction_on with
    | ind N IH =>
      intro m n hm hn hcop hlt
      by_cases hm1 : m = 1
      · subst hm1
        rw [one_mul, hg1, one_mul]
      · by_cases hn1 : n = 1
        · subst hn1
          rw [mul_one, hg1, mul_one]
        · have hm1lt : 1 < m := by omega
          have hn1lt : 1 < n := by omega
          have hSmn := squareSplitDivisors_properties.2.1 m n hcop
          have hsubm : squareSplitDivisors m ⊆ m.divisors := by
            intro d hd
            exact Nat.mem_divisors.mpr ⟨(squareSplitDivisors_properties.1 m hm).2.2 _ hd, hm⟩
          have hsubn : squareSplitDivisors n ⊆ n.divisors := by
            intro d hd
            exact Nat.mem_divisors.mpr ⟨(squareSplitDivisors_properties.1 n hn).2.2 _ hd, hn⟩
          have hsub := Finset.product_subset_product hsubm hsubn
          have hinj := hcop.mul_injOn_divisors.mono (Finset.coe_subset.mpr hsub)
          have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
          have hmn1 : m * n ≠ 1 := by
            have hm2 : 2 ≤ m := hm1lt
            have hn2 : 2 ≤ n := hn1lt
            have h4 := Nat.mul_le_mul hm2 hn2
            omega
          have hE0 : squareSplitConv f (squareSplitInv f) (m * n) = 0 := by
            rw [hfg]
            exact ArithmeticFunction.one_apply_ne hmn1
          rw [squareSplitConv_apply _ _ hmn0] at hE0
          rw [hSmn, Finset.sum_image hinj] at hE0
          have hEm : squareSplitConv f (squareSplitInv f) m = 0 := by
            rw [hfg]
            exact ArithmeticFunction.one_apply_ne hm1
          have hEn : squareSplitConv f (squareSplitInv f) n = 0 := by
            rw [hfg]
            exact ArithmeticFunction.one_apply_ne hn1
          rw [squareSplitConv_apply _ _ hm] at hEm
          rw [squareSplitConv_apply _ _ hn] at hEn
          have hterm : ∀ x ∈ (squareSplitDivisors m ×ˢ squareSplitDivisors n).erase (1, 1),
              f (x.1 * x.2) * squareSplitInv f ((m * n) / (x.1 * x.2)) =
                (f x.1 * squareSplitInv f (m / x.1)) *
                  (f x.2 * squareSplitInv f (n / x.2)) := by
            intro x hx
            obtain ⟨hne, hxmem⟩ := Finset.mem_erase.mp hx
            obtain ⟨ham', hbn'⟩ := Finset.mem_product.mp hxmem
            have ham : x.1 ∣ m := (squareSplitDivisors_properties.1 m hm).2.2 _ ham'
            have hbn : x.2 ∣ n := (squareSplitDivisors_properties.1 n hn).2.2 _ hbn'
            have ha0 : x.1 ≠ 0 := fun h => hm (by simpa [h] using ham)
            have hb0 : x.2 ≠ 0 := fun h => hn (by simpa [h] using hbn)
            have ha1 : 1 ≤ x.1 := Nat.pos_of_ne_zero ha0
            have hb1 : 1 ≤ x.2 := Nat.pos_of_ne_zero hb0
            have hne' : (x.1, x.2) ≠ (1, 1) := fun hcon => hne (Prod.mk.eta.symm.trans hcon)
            have hab1 : 1 < x.1 * x.2 := one_lt_mul_of_ne_one_one ha1 hb1 hne'
            have hfraci : f (x.1 * x.2) = f x.1 * f x.2 :=
              hf.map_mul_of_coprime (hcop.of_dvd ham hbn)
            have hdiv : (m * n) / (x.1 * x.2) = (m / x.1) * (n / x.2) :=
              (Nat.div_mul_div_comm ham hbn).symm
            have hm' : m / x.1 ≠ 0 := by
              have hle : x.1 ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) ham
              have hpos := Nat.div_pos hle (Nat.pos_of_ne_zero ha0)
              omega
            have hn' : n / x.2 ≠ 0 := by
              have hle : x.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hbn
              have hpos := Nat.div_pos hle (Nat.pos_of_ne_zero hb0)
              omega
            have hcop' : (m / x.1).Coprime (n / x.2) :=
              hcop.of_dvd (Nat.div_dvd_of_dvd ham) (Nat.div_dvd_of_dvd hbn)
            have hPlt : (m / x.1) * (n / x.2) < m * n := by
              rw [Nat.div_mul_div_comm ham hbn]
              exact Nat.div_lt_self (Nat.pos_of_ne_zero hmn0) hab1
            have hIH : squareSplitInv f ((m / x.1) * (n / x.2)) =
                squareSplitInv f (m / x.1) * squareSplitInv f (n / x.2) :=
              IH (m * n) hlt _ _ hm' hn' hcop' hPlt
            rw [hfraci, hdiv, hIH]
            ring
          have h11m : 1 ∈ squareSplitDivisors m := (squareSplitDivisors_properties.1 m hm).1
          have h11n : 1 ∈ squareSplitDivisors n := (squareSplitDivisors_properties.1 n hn).1
          have h11mem : (1, 1) ∈ squareSplitDivisors m ×ˢ squareSplitDivisors n :=
            Finset.mem_product.mpr ⟨h11m, h11n⟩
          have hsplit : ∑ x ∈ squareSplitDivisors m ×ˢ squareSplitDivisors n,
              f (x.1 * x.2) * squareSplitInv f ((m * n) / (x.1 * x.2)) =
              squareSplitInv f (m * n) + ∑ x ∈
                (squareSplitDivisors m ×ˢ squareSplitDivisors n).erase (1, 1),
                (f x.1 * squareSplitInv f (m / x.1)) *
                  (f x.2 * squareSplitInv f (n / x.2)) := by
            rw [← Finset.add_sum_erase _ _ h11mem]
            congr 1
            · show f (1 * 1) * squareSplitInv f ((m * n) / (1 * 1)) =
                squareSplitInv f (m * n)
              simp [hf1, Nat.div_one]
            · exact Finset.sum_congr rfl hterm
          rw [hsplit] at hE0
          have hprod : (∑ a ∈ squareSplitDivisors m, f a * squareSplitInv f (m / a)) *
              (∑ b ∈ squareSplitDivisors n, f b * squareSplitInv f (n / b)) =
              ∑ x ∈ squareSplitDivisors m ×ˢ squareSplitDivisors n,
                (f x.1 * squareSplitInv f (m / x.1)) *
                  (f x.2 * squareSplitInv f (n / x.2)) := by
            rw [Finset.sum_mul_sum, ← Finset.sum_product']
          have hU0 : ∑ x ∈ squareSplitDivisors m ×ˢ squareSplitDivisors n,
              (f x.1 * squareSplitInv f (m / x.1)) * (f x.2 * squareSplitInv f (n / x.2)) = 0 := by
            rw [← hprod, hEm, hEn, mul_zero]
          have hUsplit : ∑ x ∈ squareSplitDivisors m ×ˢ squareSplitDivisors n,
              (f x.1 * squareSplitInv f (m / x.1)) * (f x.2 * squareSplitInv f (n / x.2)) =
              squareSplitInv f m * squareSplitInv f n + ∑ x ∈
                (squareSplitDivisors m ×ˢ squareSplitDivisors n).erase (1, 1),
                (f x.1 * squareSplitInv f (m / x.1)) *
                  (f x.2 * squareSplitInv f (n / x.2)) := by
            rw [← Finset.add_sum_erase _ _ h11mem]
            congr 1
            · show (f 1 * squareSplitInv f (m / 1)) * (f 1 * squareSplitInv f (n / 1)) =
                squareSplitInv f m * squareSplitInv f n
              simp [hf1, Nat.div_one]
          rw [hUsplit] at hU0
          have hfinal : squareSplitInv f (m * n) =
              squareSplitInv f m * squareSplitInv f n := by
            linear_combination hE0 - hU0
          exact hfinal
  exact key (m * n + 1) m n hm hn hcop (by omega)

private theorem squareSplitU_prime_pow {p k : ℕ} (hp : p.Prime) :
    squareSplitU (p ^ k) = p ^ (k % 2) := by
  have hfact : (p ^ k).factorization = Finsupp.single p k := hp.factorization_pow
  simp [squareSplitU, hfact, Finsupp.prod_single_index]

private theorem squareSplitV_prime_pow {p k : ℕ} (hp : p.Prime) :
    squareSplitV (p ^ k) = p ^ (k / 2) := by
  have hfact : (p ^ k).factorization = Finsupp.single p k := hp.factorization_pow
  simp [squareSplitV, hfact, Finsupp.prod_single_index]

private theorem sqSplitInjOn_prime_pow {p k : ℕ} (hp : p.Prime) :
    Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2 ^ 2)
      ↑((p ^ (k % 2)).divisors ×ˢ (p ^ (k / 2)).divisors) := by
  intro x hx y hy hxy
  change x.1 * x.2 ^ 2 = y.1 * y.2 ^ 2 at hxy
  rw [Finset.mem_coe, Finset.mem_product] at hx hy
  obtain ⟨hax, hbx⟩ := hx
  obtain ⟨hay, hby⟩ := hy
  obtain ⟨e, he_le, hex⟩ := (Nat.mem_divisors_prime_pow hp (k % 2)).mp hax
  obtain ⟨j, hj_le, hjx⟩ := (Nat.mem_divisors_prime_pow hp (k / 2)).mp hbx
  obtain ⟨e', he'_le, hey⟩ := (Nat.mem_divisors_prime_pow hp (k % 2)).mp hay
  obtain ⟨j', hj'_le, hjy⟩ := (Nat.mem_divisors_prime_pow hp (k / 2)).mp hby
  have hmod2 : k % 2 < 2 := by omega
  rw [hex, hjx, hey, hjy, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add] at hxy
  have hexp : e + j * 2 = e' + j' * 2 := Nat.pow_right_injective hp.two_le hxy
  have hee : e = e' := by omega
  have hjj : j = j' := by omega
  have hx1 : x.1 = y.1 := by rw [hex, hey, hee]
  have hx2 : x.2 = y.2 := by rw [hjx, hjy, hjj]
  exact Prod.ext hx1 hx2

private theorem squareSplitConv_prime_pow_eq {f g : ArithmeticFunction ℂ} {p k : ℕ}
    (hp : p.Prime) :
    squareSplitConv f g (p ^ k) =
      ∑ a ∈ (p ^ (k % 2)).divisors, ∑ b ∈ (p ^ (k / 2)).divisors,
        f (a * b ^ 2) * g ((p ^ k) / (a * b ^ 2)) := by
  have hpk0 : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  rw [squareSplitConv_apply _ _ hpk0, squareSplitDivisors, squareSplitU_prime_pow hp,
    squareSplitV_prime_pow hp, Finset.sum_image (sqSplitInjOn_prime_pow hp), Finset.sum_product]

private theorem sum_eq_of_conv_prime_pow {f g : ArithmeticFunction ℂ}
    (hfg : squareSplitConv f g = 1) {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (k / 2 + 1), f (p ^ (2 * j)) * g (p ^ (k - 2 * j)) +
      (if Odd k then ∑ j ∈ Finset.range (k / 2 + 1),
        f (p ^ (2 * j + 1)) * g (p ^ (k - (2 * j + 1))) else 0) = 0 := by
  have hpk1 : p ^ k ≠ 1 := by
    have h1p : (1:ℕ) < p := hp.one_lt
    have h := one_lt_pow₀ h1p (show k ≠ 0 by omega)
    omega
  have hconv0 : squareSplitConv f g (p ^ k) = 0 := by
    rw [hfg]
    exact ArithmeticFunction.one_apply_ne hpk1
  rw [squareSplitConv_prime_pow_eq hp] at hconv0
  by_cases hodd : Odd k
  · rw [ite_eq_left hodd]
    have hkmod : k % 2 = 1 := Nat.odd_iff.mp hodd
    have hjbound : ∀ j ∈ Finset.range (k / 2 + 1), j ≤ k / 2 := by
      intro j hj
      have := Finset.mem_range.mp hj
      omega
    rw [hkmod, pow_one, hp.divisors] at hconv0
    have h1p : (1:ℕ) ≠ p := fun h => hp.ne_one h.symm
    rw [Finset.sum_pair h1p] at hconv0
    simp only [one_mul] at hconv0
    rw [Nat.divisors_prime_pow hp (k / 2)] at hconv0
    simp only [Finset.sum_map, Function.Embedding.coeFn_mk] at hconv0
    have hterm0 : ∀ j ∈ Finset.range (k / 2 + 1),
        f ((p ^ j) ^ 2) * g ((p ^ k) / (p ^ j) ^ 2) =
          f (p ^ (2 * j)) * g (p ^ (k - 2 * j)) := by
      intro j hj
      have h2j : 2 * j ≤ k := by
        have hjle := hjbound j hj
        omega
      have hsq : (p ^ j) ^ 2 = p ^ (2 * j) := by
        rw [← pow_mul]
        congr 1
        omega
      have hdiv : (p ^ k) / (p ^ j) ^ 2 = p ^ (k - 2 * j) := by
        rw [hsq, Nat.pow_div h2j hp.pos]
      rw [hdiv, hsq]
    have hterm1 : ∀ j ∈ Finset.range (k / 2 + 1),
        f (p * (p ^ j) ^ 2) * g ((p ^ k) / (p * (p ^ j) ^ 2)) =
          f (p ^ (2 * j + 1)) * g (p ^ (k - (2 * j + 1))) := by
      intro j hj
      have h2j1 : 2 * j + 1 ≤ k := by
        have hjle := hjbound j hj
        omega
      have hsq1 : p * (p ^ j) ^ 2 = p ^ (2 * j + 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 1
        omega
      have hdiv1 : (p ^ k) / (p * (p ^ j) ^ 2) = p ^ (k - (2 * j + 1)) := by
        rw [hsq1, Nat.pow_div h2j1 hp.pos]
      rw [hdiv1, hsq1]
    rw [Finset.sum_congr rfl hterm0, Finset.sum_congr rfl hterm1] at hconv0
    exact hconv0
  · rw [ite_eq_right hodd, add_zero]
    have hkmod : k % 2 = 0 := by
      have h1 : ¬ k % 2 = 1 := fun h => hodd (Nat.odd_iff.mpr h)
      omega
    have hjbound : ∀ j ∈ Finset.range (k / 2 + 1), j ≤ k / 2 := by
      intro j hj
      have := Finset.mem_range.mp hj
      omega
    rw [hkmod, pow_zero, Nat.divisors_one, Finset.sum_singleton] at hconv0
    simp only [one_mul] at hconv0
    rw [Nat.divisors_prime_pow hp (k / 2)] at hconv0
    simp only [Finset.sum_map, Function.Embedding.coeFn_mk] at hconv0
    have hterm0 : ∀ j ∈ Finset.range (k / 2 + 1),
        f ((p ^ j) ^ 2) * g ((p ^ k) / (p ^ j) ^ 2) =
          f (p ^ (2 * j)) * g (p ^ (k - 2 * j)) := by
      intro j hj
      have h2j : 2 * j ≤ k := by
        have hjle := hjbound j hj
        omega
      have hsq : (p ^ j) ^ 2 = p ^ (2 * j) := by
        rw [← pow_mul]
        congr 1
        omega
      have hdiv : (p ^ k) / (p ^ j) ^ 2 = p ^ (k - 2 * j) := by
        rw [hsq, Nat.pow_div h2j hp.pos]
      rw [hdiv, hsq]
    rw [Finset.sum_congr rfl hterm0] at hconv0
    exact hconv0

private theorem prime_pow_vals_of_conv {f g : ArithmeticFunction ℂ}
    (hsum : ∀ p k : ℕ, p.Prime → 1 ≤ k →
      ∑ j ∈ Finset.range (k / 2 + 1), f (p ^ (2 * j)) * g (p ^ (k - 2 * j)) +
        (if Odd k then ∑ j ∈ Finset.range (k / 2 + 1),
          f (p ^ (2 * j + 1)) * g (p ^ (k - (2 * j + 1))) else 0) = 0)
    (hg1 : g 1 = 1 / f 1) (hf1 : f 1 = 1) (p : ℕ) (hp : p.Prime) :
    g p = -f p / f 1 ^ 2 ∧ g (p ^ 2) = -f (p ^ 2) / f 1 ^ 2 ∧
      g (p ^ 3) = (2 * f p * f (p ^ 2) - f (p ^ 3) * f 1) / f 1 ^ 3 := by
  have hg1' : g 1 = 1 := by rw [hg1, hf1, div_one]
  have h12 : (1:ℕ) / 2 + 1 = 1 := by decide
  have h22 : (2:ℕ) / 2 + 1 = 2 := by decide
  have h32 : (3:ℕ) / 2 + 1 = 2 := by decide
  have hodd1 : Odd (1:ℕ) := odd_one
  have hodd2 : ¬ Odd (2:ℕ) := by decide
  have hodd3 : Odd (3:ℕ) := by decide
  have e1 := hsum p 1 hp le_rfl
  rw [h12, Finset.sum_range_one, Finset.sum_range_one, ite_eq_left hodd1] at e1
  have e1' : f 1 * g p + f p * g 1 = 0 := by simpa using e1
  rw [hf1, hg1'] at e1'
  have e2 := hsum p 2 hp (by omega)
  rw [h22, ite_eq_right hodd2, add_zero, Finset.sum_range_succ,
    Finset.sum_range_one] at e2
  have e2' : f 1 * g (p ^ 2) + f (p ^ 2) * g 1 = 0 := by simpa using e2
  rw [hf1, hg1'] at e2'
  have e3 := hsum p 3 hp (by omega)
  rw [h32, ite_eq_left hodd3, Finset.sum_range_succ, Finset.sum_range_one,
    Finset.sum_range_succ, Finset.sum_range_one] at e3
  have e3' : f 1 * g (p ^ 3) + f (p ^ 2) * g p + (f p * g (p ^ 2) + f (p ^ 3) * g 1) = 0 := by
    simpa using e3
  rw [hf1, hg1'] at e3'
  have gp : g p = -f p / f 1 ^ 2 := by
    rw [hf1]
    simp only [one_pow, div_one]
    linear_combination e1'
  have gp2 : g (p ^ 2) = -f (p ^ 2) / f 1 ^ 2 := by
    rw [hf1]
    simp only [one_pow, div_one]
    linear_combination e2'
  have gp3 : g (p ^ 3) = (2 * f p * f (p ^ 2) - f (p ^ 3) * f 1) / f 1 ^ 3 := by
    rw [hf1]
    simp only [one_pow, div_one, mul_one]
    linear_combination e3' - f (p ^ 2) * e1' - f p * e2'
  exact ⟨gp, gp2, gp3⟩

/-- **Inverse of a multiplicative function under the square-splitting convolution.** Let $f$ be a
multiplicative complex arithmetic function (an arithmetic function $h$ is multiplicative when
$h(1) = 1$ and $h(mn) = h(m)\, h(n)$ for coprime $m$ and $n$), let $\star$ be the square-splitting
convolution, and let $\varepsilon$ be the arithmetic function with $\varepsilon(1) = 1$ and
$\varepsilon(n) = 0$ for $n \ne 1$. Then there is a complex arithmetic function $g$ with
$f \star g = \varepsilon$ such that every complex arithmetic function $g'$ with
$f \star g' = \varepsilon$ equals $g$. Moreover, $g$ is multiplicative; for every prime $p$ and
every $k \ge 1$, $\sum_{j=0}^{\lfloor k/2 \rfloor} f(p^{2j})\, g(p^{k-2j}) = 0$ if $k$ is even and
$\sum_{j=0}^{\lfloor k/2 \rfloor} (f(p^{2j}) g(p^{k-2j}) + f(p^{2j+1}) g(p^{k-2j-1})) = 0$ if $k$ is
odd; $g(1) = 1/f(1)$; and for every prime $p$, $g(p) = -f(p)/f(1)^2$,
$g(p^2) = -f(p^2)/f(1)^2$ and $g(p^3) = \big(2 f(p) f(p^2) - f(p^3) f(1)\big)/f(1)^3$.

Multiplicativity includes $f(1) = 1$, so the source's hypothesis $f(1) \ne 0$ holds automatically.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 5
(`integers-2026-A56-thm-5`). -/
public theorem squareSplitConv_inverse_of_isMultiplicative {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) :
    ∃ g : ArithmeticFunction ℂ, squareSplitConv f g = 1 ∧
      (∀ g' : ArithmeticFunction ℂ, squareSplitConv f g' = 1 → g' = g) ∧
      g.IsMultiplicative ∧
      (∀ p k : ℕ, p.Prime → 1 ≤ k →
        ∑ j ∈ Finset.range (k / 2 + 1), f (p ^ (2 * j)) * g (p ^ (k - 2 * j)) +
          (if Odd k then ∑ j ∈ Finset.range (k / 2 + 1),
            f (p ^ (2 * j + 1)) * g (p ^ (k - (2 * j + 1))) else 0) = 0) ∧
      g 1 = 1 / f 1 ∧
      ∀ p : ℕ, p.Prime →
        g p = -f p / f 1 ^ 2 ∧ g (p ^ 2) = -f (p ^ 2) / f 1 ^ 2 ∧
        g (p ^ 3) = (2 * f p * f (p ^ 2) - f (p ^ 3) * f 1) / f 1 ^ 3 := by
  have hf1 : f 1 = 1 := hf.1
  have hf1ne : f 1 ≠ 0 := by rw [hf1]; exact one_ne_zero
  have hfg : squareSplitConv f (squareSplitInv f) = 1 :=
    squareSplitConv_squareSplitInv f hf1ne
  have huniq : ∀ g' : ArithmeticFunction ℂ,
      squareSplitConv f g' = 1 → g' = squareSplitInv f :=
    fun g' hg' => squareSplitConv_right_unique f (squareSplitInv f) g' hf1ne hfg hg'
  have hmult : (squareSplitInv f).IsMultiplicative := squareSplitInv_isMultiplicative hf
  have hsum : ∀ p k : ℕ, p.Prime → 1 ≤ k →
      ∑ j ∈ Finset.range (k / 2 + 1),
          f (p ^ (2 * j)) * squareSplitInv f (p ^ (k - 2 * j)) +
        (if Odd k then ∑ j ∈ Finset.range (k / 2 + 1),
          f (p ^ (2 * j + 1)) * squareSplitInv f (p ^ (k - (2 * j + 1))) else 0) = 0 :=
    fun p k hp hk => sum_eq_of_conv_prime_pow hfg hp hk
  have hg1 : squareSplitInv f 1 = 1 / f 1 := by
    rw [squareSplitInv_apply, squareSplitInvFun_apply_one, one_div]
  have hvals : ∀ p : ℕ, p.Prime →
      squareSplitInv f p = -f p / f 1 ^ 2 ∧
        squareSplitInv f (p ^ 2) = -f (p ^ 2) / f 1 ^ 2 ∧
        squareSplitInv f (p ^ 3) =
          (2 * f p * f (p ^ 2) - f (p ^ 3) * f 1) / f 1 ^ 3 :=
    fun p hp => prime_pow_vals_of_conv hsum hg1 hf1 p hp
  exact ⟨squareSplitInv f, hfg, huniq, hmult, hsum, hg1, hvals⟩

end

end MetaMathlibExt
