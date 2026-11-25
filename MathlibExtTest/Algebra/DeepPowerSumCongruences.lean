/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.DeepPowerSumCongruences
import Mathlib.NumberTheory.Zsqrtd.Basic

/-! # Tests for `MathlibExt.Algebra.DeepPowerSumCongruences` -/

namespace MathlibExtTest.DeepPowerSumCongruences

open MetaMathlibExt

/-- In any commutative ring the ideal `(p)` satisfies `a ^ p ∈ p (p)`: for `a = x p`,
`a ^ p = p (x ^ p p ^ (p - 1))` and `p ^ (p - 1) ∈ (p)` as `p - 1 ≥ 1`. -/
private theorem pow_prime_mem_span_prime {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] :
    ∀ a ∈ Ideal.span {(p : B)}, ∃ c ∈ Ideal.span {(p : B)}, a ^ p = (p : B) * c := by
  have hp : p.Prime := Fact.out
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  refine ⟨x ^ (k + 1) * ((k + 1 : ℕ) : B) ^ k, Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _
    (Ideal.mem_span_singleton_self _) _ (by have := hp.two_le; omega)), by ring⟩

-- Test section: the criterion holds. For the ideal `(p)` of any commutative ring, the theorem
-- turns the single condition above into `a ^ n ∈ p ^ v_p(n!) (p)` for every `n ≥ 1`.
example {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] :
    ∀ n : ℕ, 1 ≤ n → ∀ a ∈ Ideal.span {(p : B)}, ∃ c ∈ Ideal.span {(p : B)},
      a ^ n = (p : B) ^ padicValNat p n.factorial * c :=
  (pow_mem_prime_pow_padicValNat_factorial_iff _).2 pow_prime_mem_span_prime

-- The hypothesis `1 ≤ n` cannot be dropped: for the ideal `(2)` of `ℤ` every `n ≥ 1` works, but
-- `n = 0` would need `a ^ 0 = 1 ∈ 2 ^ v_2(0!) (2) = (2)`.
example : (∀ n : ℕ, 1 ≤ n → ∀ a ∈ Ideal.span {((2 : ℕ) : ℤ)}, ∃ c ∈ Ideal.span {((2 : ℕ) : ℤ)},
      a ^ n = ((2 : ℕ) : ℤ) ^ padicValNat 2 n.factorial * c) ∧
    ¬ ∃ c ∈ Ideal.span {((2 : ℕ) : ℤ)},
      (2 : ℤ) ^ 0 = ((2 : ℕ) : ℤ) ^ padicValNat 2 (Nat.factorial 0) * c := by
  refine ⟨(pow_mem_prime_pow_padicValNat_factorial_iff _).2 pow_prime_mem_span_prime, ?_⟩
  rintro ⟨c, hc, h⟩
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  simp [Nat.padicValNat_def] at h
  omega

-- Test section: the criterion fails. The unit ideal of `ℤ` does not have `1 ^ 3 ∈ 3 ℤ`, so by the
-- theorem some `a ^ n` is not in `3 ^ v_3(n!) ℤ`.
example : ¬ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ (⊤ : Ideal ℤ), ∃ c ∈ (⊤ : Ideal ℤ),
    a ^ n = ((3 : ℕ) : ℤ) ^ padicValNat 3 n.factorial * c := by
  rw [pow_mem_prime_pow_padicValNat_factorial_iff]
  intro h
  obtain ⟨c, -, hc⟩ := h 1 Submodule.mem_top
  simp at hc
  omega

-- In `ℤ√2` the ideal `(√2)` fails the criterion for `p = 2`: `√2 ^ 2 = 2`, but every element of
-- `2 (√2)` has rational part divisible by `4`. So, by the theorem, some power of an element of
-- `(√2)` is not in `2 ^ v_2(n!) (√2)`.
example : ¬ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ Ideal.span {(Zsqrtd.sqrtd : ℤ√2)},
    ∃ c ∈ Ideal.span {(Zsqrtd.sqrtd : ℤ√2)},
      a ^ n = ((2 : ℕ) : ℤ√2) ^ padicValNat 2 n.factorial * c := by
  rw [pow_mem_prime_pow_padicValNat_factorial_iff]
  intro h
  obtain ⟨c, hc, hsq⟩ := h _ (Ideal.mem_span_singleton_self _)
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  have hre := congrArg Zsqrtd.re hsq
  simp [pow_two] at hre
  omega

-- Test section: Kummer's theorem for multinomial coefficients.

/-- The binomial case: `v_p(C(n + k, k))` is the sum over `1 ≤ i ≤ n + k` of the carries
`⌊(k mod p ^ i + n mod p ^ i) / p ^ i⌋`, from the multinomial coefficient `(n + k; k, n)` of a
two-element index set. -/
private theorem padicValNat_choose_eq_sum_carries {p : ℕ} [Fact p.Prime] (n k : ℕ) :
    padicValNat p ((n + k).choose k) =
      ∑ i ∈ Finset.Icc 1 (n + k), (k % p ^ i + n % p ^ i) / p ^ i := by
  have h := padicValNat_multinomial_eq_sum_carries (p := p) ({0, 1} : Finset (Fin 2)) ![k, n]
  rw [Nat.binomial_eq_choose (by decide)] at h
  simpa [Finset.sum_pair, Nat.add_comm k n] using h

-- With two numbers every carry is `0` or `1`, so the sum of the carries counts the positions `i`
-- with `p ^ i ≤ k mod p ^ i + n mod p ^ i`: this is Kummer's theorem for binomial coefficients,
-- in the form of Mathlib's `multiplicity_choose'`.
open Finset in
example {p : ℕ} [hp : Fact p.Prime] (n k : ℕ) :
    padicValNat p ((n + k).choose k) = #{i ∈ Icc 1 (n + k) | p ^ i ≤ k % p ^ i + n % p ^ i} := by
  rw [padicValNat_choose_eq_sum_carries, card_filter]
  refine sum_congr rfl fun i _ => ?_
  have hpi : 0 < p ^ i := pow_pos hp.out.pos i
  have hk := Nat.mod_lt k hpi
  have hn := Nat.mod_lt n hpi
  split_ifs with h
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt (by omega)

-- With more numbers a carry can exceed `1`: for `p = 2` and `r = (1, 1, 1, 1)` the carries are
-- `c_1 = 2` and `c_2 = 1`, and indeed `(4; 1, 1, 1, 1) = 24 = 2 ^ 3 * 3`.
example : padicValNat 2 (Nat.multinomial Finset.univ ![1, 1, 1, 1]) = 3 ∧
    (∑ j : Fin 4, ![1, 1, 1, 1] j % 2 ^ 1) / 2 ^ 1 = 2 ∧
    Nat.multinomial Finset.univ ![1, 1, 1, 1] = 2 ^ 3 * 3 := by
  refine ⟨?_, by decide, by decide⟩
  rw [padicValNat_multinomial_eq_sum_carries]
  decide

-- The carries vanish beyond `m = Σ_j r_j`, so the sum over `1 ≤ i ≤ m` is the sum of all the
-- carries: for `i > m`, every `r_j ≤ m < p ^ i`, so `Σ_j (r_j mod p ^ i) = m < p ^ i`.
example {p : ℕ} [hp : Fact p.Prime] {ι : Type*} (s : Finset ι) (r : ι → ℕ) {i : ℕ}
    (hi : ∑ j ∈ s, r j < i) : (∑ j ∈ s, r j % p ^ i) / p ^ i = 0 := by
  have hlt : ∑ j ∈ s, r j < p ^ i := hi.trans (Nat.lt_pow_self hp.out.one_lt)
  rw [Finset.sum_congr rfl fun j hj => Nat.mod_eq_of_lt
    ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj).trans_lt hlt)]
  exact Nat.div_eq_of_lt hlt

-- Test section: the valuation bound for multinomial coefficients.

/-- The binomial case of the bound, `v_p(n) ≤ v_p(k) + v_p(C(n, k))` for `0 < k ≤ n`, from the
multinomial coefficient `(n; k, n - k) = C(n, k)` of a two-element index set. -/
private theorem padicValNat_le_add_padicValNat_choose {p : ℕ} [Fact p.Prime] {n k : ℕ}
    (hk : k ≠ 0) (hkn : k ≤ n) :
    padicValNat p n ≤ padicValNat p k + padicValNat p (n.choose k) := by
  have h := padicValNat_sum_le_add_padicValNat_multinomial (p := p) ({0, 1} : Finset (Fin 2))
    ![k, n - k] (Finset.mem_insert_self 0 _) hk
  rw [Nat.binomial_eq_choose (by decide), Finset.sum_pair (by decide)] at h
  simpa [Nat.add_sub_cancel' hkn] using h

-- A classical consequence: `p` divides `C(p ^ a, k)` for `0 < k < p ^ a`, as `v_p(k) < a`.
example {p a k : ℕ} [hp : Fact p.Prime] (hk : k ≠ 0) (hka : k < p ^ a) :
    p ∣ (p ^ a).choose k := by
  have h := padicValNat_le_add_padicValNat_choose (p := p) hk hka.le
  simp only [Nat.padicValNat_def, Nat.multiplicity_prime_pow] at h
  have hlt : multiplicity p k < a :=
    (Nat.pow_lt_pow_iff_right hp.out.one_lt).1
      ((Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (pow_multiplicity_dvd p k)).trans_lt hka)
  exact dvd_of_one_le_multiplicity (by omega)

-- The bound is sharp: for `p = 2` and `r = (2, 2)`, `v_2(4) = 2`, `v_2(2) = 1` and
-- `(4; 2, 2) = 6` has `v_2(6) = 1`, so the theorem's `2 ≤ 1 + 1` is an equality.
example : padicValNat 2 (∑ i : Fin 2, ![2, 2] i) ≤
      padicValNat 2 (![2, 2] 0) + padicValNat 2 (Nat.multinomial Finset.univ ![2, 2]) ∧
    padicValNat 2 (∑ i : Fin 2, ![2, 2] i) = 2 ∧ padicValNat 2 (![2, 2] 0) = 1 ∧
    padicValNat 2 (Nat.multinomial Finset.univ ![2, 2]) = 1 := by
  refine ⟨padicValNat_sum_le_add_padicValNat_multinomial _ _ (Finset.mem_univ 0) (by decide),
    ?_, by simp [Nat.padicValNat_def, Nat.multiplicity_self], ?_⟩
  · have hsum : ∑ i : Fin 2, ![2, 2] i = 2 ^ 2 := by simp [Fin.sum_univ_two]
    rw [hsum, Nat.padicValNat_def, Nat.multiplicity_prime_pow]
  · have hmul : Nat.multinomial Finset.univ ![2, 2] = 2 * 3 := by decide
    rw [hmul, Nat.padicValNat_def, Nat.multiplicity_mul (by norm_num) (by norm_num),
      Nat.multiplicity_self (by norm_num), multiplicity_eq_zero_of_not_dvd (by norm_num)]

-- The hypothesis `r j ≠ 0` cannot be dropped: for `r = (0, 2)` and `j = 0`, `v_2(0 + 2) = 1`,
-- while `v_2(0) = 0` (Mathlib's convention) and `(2; 0, 2) = 1`.
example : ¬ padicValNat 2 (∑ i : Fin 2, ![0, 2] i) ≤
    padicValNat 2 (![0, 2] 0) + padicValNat 2 (Nat.multinomial Finset.univ ![0, 2]) := by
  have hsum : ∑ i : Fin 2, ![0, 2] i = 2 := by simp [Fin.sum_univ_two]
  have hmul : Nat.multinomial Finset.univ ![0, 2] = 1 := by decide
  simp [hsum, hmul, Nat.padicValNat_def, Nat.multiplicity_self]

end MathlibExtTest.DeepPowerSumCongruences
