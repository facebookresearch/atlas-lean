/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.PadicValNat
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.Positivity
import MathlibExt.NumberTheory.WolstenholmeBinomialExtension

/-!
# The Helou–Terjanian congruence at two

`MetaMathlibExt.choose_two_mul_modEq` gives a lower bound on the 2-adic valuation of the
difference between a binomial coefficient and the coefficient with both arguments doubled.
-/

namespace MetaMathlibExt

private def oddProduct (a k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (2 * a + (2 * i + 1))

-- Specialize the prime-index product formula and clear its odd denominator.
private theorem choose_mul_oddProduct (a k : ℕ) (hk : 0 < k) :
    (2 * (a + k)).choose (2 * k) * oddProduct 0 k = (a + k).choose k * oddProduct a k := by
  have h := (choose_mul_prime_eq_prod_div_prod 2 k (a + k) Nat.prime_two hk
    (Nat.le_add_left k a)).1
  have oddIndex (i : ℕ) : (i + 1) * 2 - 1 = 2 * i + 1 := by omega
  simp only [Nat.add_sub_cancel, Nat.reduceSub, oddIndex, Nat.choose_one_right] at h
  have hd : (∏ j ∈ Finset.range k, ((2 * j + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  have hnat := (eq_div_iff hd).mp h
  norm_cast at hnat
  simpa only [oddProduct, mul_zero, zero_add, Nat.mul_add, Nat.add_assoc,
    Nat.mul_comm 2 (a + k), Nat.mul_comm 2 k] using hnat

-- Each numerator factor differs from its denominator factor by 2a.
private theorem choose_two_mul_modEq_add (a k : ℕ) (hk : 0 < k) :
    (2 * (a + k)).choose (2 * k) ≡ (a + k).choose k
      [MOD 2 ^ (1 + padicValNat 2 a + padicValNat 2 ((a + k).choose k))] := by
  simp only [Nat.padicValNat_def]
  have hshift : 2 ^ (1 + multiplicity 2 a) ∣ 2 * a := by
    rw [pow_add, pow_one]
    exact Nat.mul_dvd_mul_left 2 (pow_multiplicity_dvd _ _)
  have hprod : oddProduct a k ≡ oddProduct 0 k [MOD 2 ^ (1 + multiplicity 2 a)] := by
    apply Nat.ModEq.prod
    intro i _
    simpa using (Nat.modEq_zero_iff_dvd.mpr hshift).add_right (2 * i + 1)
  have hcop : Nat.Coprime 2 (oddProduct 0 k) := by
    apply Nat.Coprime.prod_right
    intro i _
    exact Nat.coprime_two_left.mpr ⟨i, by simp⟩
  apply Nat.ModEq.cancel_right_of_coprime (hcop.pow_left _)
  rw [choose_mul_oddProduct a k hk]
  -- Multiplication by the binomial coefficient contributes its own power of two.
  apply (hprod.mul_left' _).of_dvd
  rw [pow_add, mul_comm]
  exact mul_dvd_mul_right (pow_multiplicity_dvd _ _) _

/-- **Helou–Terjanian congruence for $p = 2$.** Let $m$ and $n$ be integers with $0 < m < n$.
Then $\binom{2n}{2m} \equiv \binom{n}{m} \pmod{2^e}$, where
$e = 1 + \max(\nu_2(m), \nu_2(n - m)) + \nu_2\big(\binom{n}{m}\big)$ and $\nu_2$ is the $2$-adic
valuation.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Lemma 26 (3) (`jis-2024-24.3.3-lem-26`). -/
public theorem choose_two_mul_modEq (n m : ℕ) (hm : 0 < m) (hmn : m < n) :
    (2 * n).choose (2 * m) ≡ n.choose m
      [MOD 2 ^ (1 + max (padicValNat 2 m) (padicValNat 2 (n - m)) +
        padicValNat 2 (n.choose m))] := by
  have hsum : n - m + m = n := Nat.sub_add_cancel hmn.le
  rcases le_total (padicValNat 2 m) (padicValNat 2 (n - m)) with h | h
  · rw [max_eq_right h]
    simpa only [hsum] using choose_two_mul_modEq_add (n - m) m hm
  · rw [max_eq_left h]
    have hchoose := Nat.choose_symm hmn.le
    have hdouble : (2 * n).choose (2 * (n - m)) = (2 * n).choose (2 * m) := by
      rw [Nat.mul_sub, Nat.choose_symm (by omega)]
    simpa only [Nat.add_sub_of_le hmn.le, hchoose, hdouble] using
      choose_two_mul_modEq_add m (n - m) (Nat.sub_pos_of_lt hmn)

end MetaMathlibExt
