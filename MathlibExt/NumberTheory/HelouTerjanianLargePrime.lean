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
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.WolstenholmeBinomialExtension

/-!
# The Helou–Terjanian congruence at primes at least five

`MetaMathlibExt.choose_mul_prime_modEq_of_five_le` shows that for a prime `p ≥ 5` and natural
numbers `0 < m < n`, the binomial coefficients `(n * p).choose (m * p)` and `n.choose m` are
congruent modulo `p ^ e` with `e = 3 + max (ν_p m) (ν_p (n - m)) + ν_p (n.choose m)`, where `ν_p`
is the `p`-adic valuation.

## Proof idea

Let `F c` be the product of the `p - 1` integers strictly between `c * p` and `(c + 1) * p`.
Collecting the factors of `((a + k) * p).choose (k * p)` by blocks of `p` consecutive integers
gives `((a + k) * p).choose (k * p) * ∏ F j = (a + k).choose k * ∏ F (a + j)`, the products over
`j < k`, and each `F j` is prime to `p`. Pairing `r` with `p - r` writes `(F c) ^ 2` as the product
of the factors `r * (p - r) + c * (c + 1) * p ^ 2`, and passing from `c` to `a + c` adds
`D = a * (a + 2 * c + 1) * p ^ 2` to each factor. Expanding the product to first order in `D` and
using that the inverse squares of `1, …, p - 1` sum to `0` modulo `p` when `p ≥ 5` shows that
`p * D` divides `F (a + c) ^ 2 - F c ^ 2`. As `F (a + c) + F c` is prime to `p`, this gives
`F (a + c) ≡ F c` modulo `p ^ (3 + ν_p a)`. Multiplying by `(a + k).choose k` adds its valuation
to the exponent; exchanging `m` and `n - m` gives the maximum.
-/

namespace MetaMathlibExt

namespace choose_mul_prime_modEq_of_five_le

/-- The product of the `p - 1` integers strictly between `c * p` and `(c + 1) * p`. -/
private def blockProd (p c : ℕ) : ℕ :=
  ∏ r ∈ Finset.Ico 1 p, (c * p + r)

-- A block product is `(p - 1)!` times a binomial coefficient with lower index `p - 1`.
private theorem blockProd_eq (p c : ℕ) (hp : 0 < p) :
    blockProd p c = (p - 1).factorial * ((c + 1) * p - 1).choose (p - 1) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose (c * p) (p - 1)
  rw [Nat.ascFactorial_eq_prod_range,
    show c * p + (p - 1) = (c + 1) * p - 1 by rw [Nat.add_mul, one_mul]; omega] at h
  rw [← h, blockProd, Finset.prod_Ico_eq_prod_range]
  exact Finset.prod_congr rfl fun i _ => by ring

-- Pairing `r` with `p - r` turns the square of a block product into quadratic factors.
private theorem blockProd_sq (p c : ℕ) :
    (blockProd p c : ℤ) ^ 2 =
      ∏ r ∈ Finset.Ico 1 p, ((r : ℤ) * (p - r) + c * (c + 1) * p ^ 2) := by
  have hrefl : ∏ r ∈ Finset.Ico 1 p, ((c : ℤ) * p + r) =
      ∏ r ∈ Finset.Ico 1 p, ((c : ℤ) * p + (p - r)) := by
    have h := Finset.prod_Ico_reflect (fun j => (c : ℤ) * p + j) 1 (Nat.le_succ p)
    simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel] at h
    rw [← h]
    exact Finset.prod_congr rfl fun r hr => by rw [Nat.cast_sub (Finset.mem_Ico.mp hr).2.le]
  rw [sq, blockProd]
  push_cast
  nth_rewrite 2 [hrefl]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun r _ => by ring

-- First-order expansion of a product, with the coefficient of `D` computed modulo `p`.
private theorem exists_prod_add_sub_prod (p : ℕ) [Fact p.Prime] (s : Finset ℕ) (y : ℕ → ℤ)
    (D : ℤ) (hD : (p : ℤ) ∣ D) (hy : ∀ r ∈ s, (y r : ZMod p) ≠ 0) :
    ∃ T : ℤ, ∏ r ∈ s, (y r + D) - ∏ r ∈ s, y r = D * T ∧
      (T : ZMod p) = (∏ r ∈ s, (y r : ZMod p)) * ∑ r ∈ s, (y r : ZMod p)⁻¹ := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert i s hi ih =>
    obtain ⟨T, hT, hTp⟩ := ih fun r hr => hy r (Finset.mem_insert_of_mem hr)
    have hyi : (y i : ZMod p) * (y i : ZMod p)⁻¹ = 1 :=
      mul_inv_cancel₀ (hy i (Finset.mem_insert_self i s))
    have hD0 : (D : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr hD
    refine ⟨(y i + D) * T + ∏ r ∈ s, y r, ?_, ?_⟩
    · rw [Finset.prod_insert hi, Finset.prod_insert hi]
      linear_combination (y i + D) * hT
    · rw [Finset.prod_insert hi, Finset.sum_insert hi]
      push_cast
      rw [hTp, hD0, add_zero]
      linear_combination (-∏ r ∈ s, (y r : ZMod p)) * hyi

-- The residues of `1, …, p - 1` are nonzero.
private theorem natCast_ne_zero_of_mem_Ico {p r : ℕ} (hr : r ∈ Finset.Ico 1 p) :
    (r : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hr
  exact fun h => absurd (Nat.le_of_dvd h1 h) (not_le.mpr h2)

-- A sum over `Finset.range p` of a function of the residue is a sum over `ZMod p`.
private theorem sum_range_natCast {M : Type*} [AddCommMonoid M] (p : ℕ) [NeZero p]
    (φ : ZMod p → M) : ∑ i ∈ Finset.range p, φ (i : ZMod p) = ∑ x, φ x := by
  apply Finset.sum_bij (fun (i : ℕ) _ => (i : ZMod p))
  · exact fun _ _ => Finset.mem_univ _
  · intro i hi j hj h
    exact Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff i j p).mp h)
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
  · exact fun x _ => ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
  · exact fun _ _ => rfl

-- For `p ≥ 5` the inverse squares of `1, …, p - 1` sum to zero modulo `p`.
private theorem sum_inv_sq_eq_zero (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ r ∈ Finset.Ico 1 p, ((r : ZMod p) ^ 2)⁻¹ = 0 := by
  have hrange : ∑ r ∈ Finset.range p, ((r : ZMod p) ^ 2)⁻¹ =
      ∑ r ∈ Finset.Ico 1 p, ((r : ZMod p) ^ 2)⁻¹ := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp.out.pos]
    simp
  -- Inversion permutes the residues, so this is the sum of the squares.
  rw [← hrange, sum_range_natCast p fun x => (x ^ 2)⁻¹, ← Equiv.sum_comp (Equiv.inv (ZMod p))]
  simp only [Equiv.inv_apply, inv_pow, inv_inv]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 (by rw [ZMod.card]; omega)

-- Shifting a block by `a` places changes its product by a multiple of `p ^ (3 + ν_p a)`.
private theorem blockProd_modEq (p a c : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    blockProd p (a + c) ≡ blockProd p c [MOD p ^ (3 + padicValNat p a)] := by
  have := Fact.mk hp
  let y : ℕ → ℤ := fun r => (r : ℤ) * (p - r) + c * (c + 1) * p ^ 2
  let D : ℤ := a * (a + 2 * c + 1) * p ^ 2
  have hpD : (p : ℤ) ∣ D := ⟨a * (a + 2 * c + 1) * p, by ring⟩
  have hres (r : ℕ) : (y r : ZMod p) = -((r : ZMod p) ^ 2) := by
    simp only [y]
    push_cast
    rw [ZMod.natCast_self]
    ring
  have hunit : ∀ r ∈ Finset.Ico 1 p, (y r : ZMod p) ≠ 0 := fun r hr => by
    rw [hres, neg_ne_zero]
    exact pow_ne_zero 2 (natCast_ne_zero_of_mem_Ico hr)
  obtain ⟨T, hT, hTp⟩ := exists_prod_add_sub_prod p (Finset.Ico 1 p) y D hpD hunit
  have hpT : (p : ℤ) ∣ T := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hTp]
    simp only [hres, inv_neg, Finset.sum_neg_distrib, sum_inv_sq_eq_zero p hp5, neg_zero,
      mul_zero]
  -- The difference of the two block products, times their sum, is `D * T`.
  have hsq : ((blockProd p (a + c) : ℤ) - blockProd p c) *
      ((blockProd p (a + c) : ℤ) + blockProd p c) = D * T := by
    have h1 := blockProd_sq p (a + c)
    have h0 := blockProd_sq p c
    have hshift : ∏ r ∈ Finset.Ico 1 p,
        ((r : ℤ) * (p - r) + ((a + c : ℕ) : ℤ) * ((a + c : ℕ) + 1) * p ^ 2) =
          ∏ r ∈ Finset.Ico 1 p, (y r + D) :=
      Finset.prod_congr rfl fun r _ => by simp only [y, D]; push_cast; ring
    rw [hshift] at h1
    linear_combination h1 - h0 + hT
  have hdvd : (p : ℤ) ^ (3 + padicValNat p a) ∣ D * T := by
    obtain ⟨T', hT'⟩ := hpT
    obtain ⟨b, hb⟩ : p ^ padicValNat p a ∣ a :=
      Dvd.intro_left _ (Nat.divMaxPow_mul_pow_padicValNat p a)
    refine ⟨b * (a + 2 * c + 1) * T', ?_⟩
    simp only [D, hT']
    rw [pow_add]
    nth_rewrite 1 [hb]
    push_cast
    ring
  -- The sum of the two block products is prime to `p`.
  have hcop : IsCoprime ((p : ℤ) ^ (3 + padicValNat p a))
      ((blockProd p (a + c) : ℤ) + blockProd p c) := by
    have hres' (A : ℕ) : (blockProd p A : ZMod p) = ∏ r ∈ Finset.Ico 1 p, (r : ZMod p) := by
      simp [blockProd]
    have hnd : ¬ p ∣ blockProd p (a + c) + blockProd p c := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, hres', hres', ← two_mul]
      refine mul_ne_zero ?_
        (Finset.prod_ne_zero_iff.mpr fun r hr => natCast_ne_zero_of_mem_Ico hr)
      exact_mod_cast natCast_ne_zero_of_mem_Ico (p := p) (r := 2)
        (Finset.mem_Ico.mpr ⟨by norm_num, by omega⟩)
    have h := Nat.isCoprime_iff_coprime.mpr
      (((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).pow_left (3 + padicValNat p a))
    exact_mod_cast h
  have hdiff := hcop.dvd_of_dvd_mul_right (hsq.symm ▸ hdvd)
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd]
  exact_mod_cast hdiff

-- Cross-multiplied form of the block quotient formula for `((a + k) * p).choose (k * p)`.
private theorem choose_mul_prod_blockProd (p a k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    ((a + k) * p).choose (k * p) * ∏ j ∈ Finset.range k, blockProd p j =
      (a + k).choose k * ∏ j ∈ Finset.range k, blockProd p (a + j) := by
  have h := (choose_mul_prime_eq_prod_div_prod p k (a + k) hp hk (Nat.le_add_left k a)).1
  simp only [Nat.add_sub_cancel] at h
  have hd : (∏ j ∈ Finset.range k, (((j + 1) * p - 1).choose (p - 1) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by
      have hle : p ≤ (j + 1) * p := Nat.le_mul_of_pos_left p (Nat.succ_pos j)
      exact_mod_cast (Nat.choose_pos (Nat.sub_le_sub_right hle 1)).ne'
  rw [eq_div_iff hd] at h
  have hnat : ((a + k) * p).choose (k * p) *
      ∏ j ∈ Finset.range k, ((j + 1) * p - 1).choose (p - 1) =
        (a + k).choose k * ∏ j ∈ Finset.range k, ((a + j + 1) * p - 1).choose (p - 1) := by
    exact_mod_cast h
  simp only [blockProd_eq p _ hp.pos, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range]
  rw [mul_left_comm, hnat, mul_left_comm]

-- The congruence with the valuation of the complementary index `a` in the exponent.
private theorem choose_mul_modEq_add (p a k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    ((a + k) * p).choose (k * p) ≡ (a + k).choose k
      [MOD p ^ (3 + padicValNat p a + padicValNat p ((a + k).choose k))] := by
  have hprod : ∏ j ∈ Finset.range k, blockProd p (a + j) ≡
      ∏ j ∈ Finset.range k, blockProd p j [MOD p ^ (3 + padicValNat p a)] :=
    Nat.ModEq.prod fun j _ => blockProd_modEq p a j hp hp5
  have hcop : Nat.Coprime p (∏ j ∈ Finset.range k, blockProd p j) :=
    Nat.Coprime.prod_right fun j _ => Nat.Coprime.prod_right fun r hr => by
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hr
      rw [Nat.mul_comm, Nat.coprime_mul_left_add_right]
      exact Nat.coprime_of_lt_prime (by omega) h2 hp
  apply Nat.ModEq.cancel_right_of_coprime (hcop.pow_left _)
  rw [choose_mul_prod_blockProd p a k hp hk]
  -- Multiplication by the binomial coefficient contributes its own power of `p`.
  apply (hprod.mul_left' _).of_dvd
  rw [pow_add, mul_comm]
  exact mul_dvd_mul_right (Dvd.intro_left _ (Nat.divMaxPow_mul_pow_padicValNat p _)) _

end choose_mul_prime_modEq_of_five_le

open choose_mul_prime_modEq_of_five_le

/-- **Helou–Terjanian congruence for primes $p \ge 5$.** Let $p \ge 5$ be a prime and let $m$ and
$n$ be integers with $0 < m < n$. Then $\binom{np}{mp} \equiv \binom{n}{m} \pmod{p^e}$, where
$e = 3 + \max(\nu_p(m), \nu_p(n - m)) + \nu_p\big(\binom{n}{m}\big)$ and $\nu_p$ is the $p$-adic
valuation.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Lemma 26 (1) (`jis-2024-24.3.3-lem-26`). -/
public theorem choose_mul_prime_modEq_of_five_le (p n m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 0 < m) (hmn : m < n) :
    (n * p).choose (m * p) ≡ n.choose m
      [MOD p ^ (3 + max (padicValNat p m) (padicValNat p (n - m)) +
        padicValNat p (n.choose m))] := by
  have hsum : n - m + m = n := Nat.sub_add_cancel hmn.le
  rcases le_total (padicValNat p m) (padicValNat p (n - m)) with h | h
  · rw [max_eq_right h]
    simpa only [hsum] using choose_mul_modEq_add p (n - m) m hp hp5 hm
  · rw [max_eq_left h]
    have hchoose := Nat.choose_symm hmn.le
    have hmul : (n * p).choose ((n - m) * p) = (n * p).choose (m * p) := by
      rw [Nat.sub_mul, Nat.choose_symm (Nat.mul_le_mul_right p hmn.le)]
    simpa only [Nat.add_sub_of_le hmn.le, hchoose, hmul] using
      choose_mul_modEq_add p m (n - m) hp hp5 (Nat.sub_pos_of_lt hmn)

end MetaMathlibExt
