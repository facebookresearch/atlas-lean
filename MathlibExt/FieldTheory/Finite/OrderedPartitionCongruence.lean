/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum

/-!
# Vishwakarma–Singh congruence for ordered partitions

`MetaMathlibExt.prime_dvd_sum_compositions_prod_pow` proves that the sum of the weighted
ordered partitions with total divisible by `p - 1` vanishes modulo `p` in the stated range.

Grouping terms into blocks of length `p` shows that the generating polynomial takes the value
`x` at every unit `x`. Summing its `s`-th power over the units selects the tuples whose total
is a multiple of `p - 1`.

## References

* C. K. Vishwakarma and R. P. Singh, *A Congruence Identity on Ordered Partitions Using Permutation
  Polynomials*, INTEGERS 24 (2024), Article A12, Theorem 1 and Corollary 2 (the linear case).
* R. P. Singh and M. K. Singh, *Two Congruence Identities on Ordered Partitions*, INTEGERS 18
  (2018), Article A73, Theorem 1, cited by Vishwakarma and Singh for the linear congruence.
* R. Lidl and H. Niederreiter, *Finite Fields*, 2nd ed., Cambridge University Press (1997),
  Theorem 7.6, the source for Hermite's criterion in the paper's proof.
-/

namespace MetaMathlibExt

open Finset

namespace OrderedPartitionCongruence

private theorem sum_range_pow {p : ℕ} [Fact p.Prime] {t : ℕ} (ht : 0 < t) :
    ∑ r ∈ range p, (r : ZMod p) ^ t = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ t := by
  symm
  apply sum_bij_ne_zero (fun (u : (ZMod p)ˣ) _ _ => (u : ZMod p).val)
  · exact fun u _ _ => mem_range.mpr (ZMod.val_lt _)
  · intro a _ _ b _ _ h
    exact Units.ext (ZMod.val_injective p h)
  · intro r hr h
    have hr₀ : (r : ZMod p) ≠ 0 := fun e => h (by rw [e, zero_pow ht.ne'])
    refine ⟨Units.mk0 (r : ZMod p) hr₀, mem_univ _, h, ?_⟩
    exact ZMod.val_cast_of_lt (mem_range.mp hr)
  · intro u _ _
    simp

-- Each block of length p has the same coefficients. Its powers of x acquire a factor of x^j.
private theorem sum_blocks {p : ℕ} [Fact p.Prime] (x : ZMod p) (t m : ℕ) :
    ∑ n ∈ range (p * m), (n : ZMod p) ^ t * x ^ n =
      (∑ r ∈ range p, (r : ZMod p) ^ t * x ^ r) * ∑ j ∈ range m, x ^ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ, mul_add]
    congr 1
    rw [sum_mul]
    apply sum_congr rfl
    intro r _
    simp [pow_add, pow_mul, ZMod.pow_card, mul_comm, mul_assoc]

private theorem weighted_sum_eq_self {p : ℕ} [Fact p.Prime] {k t : ℕ}
    (hk : 0 < k) (ht : 0 < t) (hkcong : k ≡ 1 [MOD p * (p - 1)])
    (hcases : (p - 1) ∣ t → p ^ 2 ∣ k - 1) (x : (ZMod p)ˣ) :
    ∑ n ∈ Icc 1 k, (n : ZMod p) ^ t * (x : ZMod p) ^ n = x := by
  obtain ⟨b, hb⟩ := hkcong.symm.dvd'
  let m := (p - 1) * b
  have hkm : k = p * m + 1 := by
    rw [Nat.mul_assoc] at hb
    change k = p * ((p - 1) * b) + 1
    omega
  have hxm : (x : ZMod p) ^ m = 1 := by
    rw [show m = (p - 1) * b from rfl, pow_mul, ZMod.pow_card_sub_one_eq_one x.ne_zero, one_pow]
  have hblocks : (∑ r ∈ range p, (r : ZMod p) ^ t * (x : ZMod p) ^ r) *
      ∑ j ∈ range m, (x : ZMod p) ^ j = 0 := by
    by_cases hx : (x : ZMod p) = 1
    · simp only [hx, one_pow, mul_one, sum_const, card_range, nsmul_eq_mul]
      by_cases h : p - 1 ∣ t
      · have hd : p ∣ m := Nat.dvd_of_mul_dvd_mul_left (Fact.out : p.Prime).pos
          (by simpa [pow_two, hkm] using hcases h)
        simp [(ZMod.natCast_eq_zero_iff m p).2 hd]
      · simp [sum_range_pow ht, FiniteField.sum_pow_units, ZMod.card, h]
    · simp [geom_sum_eq hx, hxm]
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sub _ (by omega), hkm,
    sum_range_succ _ (p * m + 1), sum_range_succ _ (p * m), sum_blocks, hblocks]
  simp [pow_succ, pow_mul, ZMod.pow_card, hxm, ht.ne']

private theorem sum_multiples {p n d B : ℕ} (hn : 0 < n) (hd : 0 < d) (hB : n ≤ B)
    (a : ZMod p) :
    ∑ j ∈ Icc 1 (B / d), (if n = j * d then a else 0) = if d ∣ n then a else 0 := by
  by_cases h : d ∣ n
  · obtain ⟨q, rfl⟩ := h
    have hq : q ∈ Icc 1 (B / d) := by
      refine mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left hn, (Nat.le_div_iff_mul_le hd).2 ?_⟩
      rwa [Nat.mul_comm]
    simp [Nat.mul_comm d q, Nat.mul_left_inj hd.ne', sum_ite_eq, hq]
  · have hne (j : ℕ) : n ≠ j * d := fun e => h (e ▸ dvd_mul_left d j)
    simp [hne, h]

end OrderedPartitionCongruence

open OrderedPartitionCongruence

/-- **Vishwakarma–Singh congruence for ordered partitions.** Let $p$ be an odd prime and let
$k, s, t$ be positive integers with $s \le p - 2$ and $k \equiv 1 \pmod{p(p-1)}$, such that
$p^2 \mid k - 1$ whenever $p - 1 \mid t$. Let $\mu = \lfloor ks/(p - 1) \rfloor$. Then

$$\sum_{j=1}^{\mu} \sum_{\omega} (\omega_1 \cdots \omega_s)^t \equiv 0 \pmod{p},$$

where for each $j$ the inner sum runs over all $s$-tuples $\omega = (\omega_1, \dots, \omega_s)$
with entries in $\{1, \dots, k\}$ and $\omega_1 + \cdots + \omega_s = j(p - 1)$.

The source states the hypothesis $s \not\equiv 0 \pmod{p}$ in place of $s \le p - 2$, the range
of Hermite's criterion used in its proof; with that hypothesis the claim fails, e.g. for $p = 3$,
$k = 1$, $s = 2$, $t = 1$ the sum is $1$.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Theorem 1
(`integers-2024-A12-thm-1`). -/
public theorem prime_dvd_sum_compositions_prod_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {k s t : ℕ} (hk : 0 < k) (hs : 0 < s) (hsp : s ≤ p - 2) (ht : 0 < t)
    (hkcong : k ≡ 1 [MOD p * (p - 1)]) (hcases : (p - 1) ∣ t → p ^ 2 ∣ k - 1) :
    p ∣ ∑ j ∈ Finset.Icc 1 (k * s / (p - 1)),
      ∑ ω ∈ (Fintype.piFinset fun _ : Fin s => Finset.Icc 1 k).filter
          (fun ω => ∑ i, ω i = j * (p - 1)),
        (∏ i, ω i) ^ t := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := lt_of_le_of_ne hp.two_le hp2.symm
  let tuples := Fintype.piFinset fun _ : Fin s => Icc 1 k
  let weight (ω : Fin s → ℕ) : ZMod p := (∏ i, (ω i : ZMod p)) ^ t
  -- The sum of the expanded s-th powers equals the sum of the s-th powers of the units.
  have hmoment : ∑ x : (ZMod p)ˣ, ∑ ω ∈ tuples, weight ω * (x : ZMod p) ^ (∑ i, ω i) = 0 := by
    calc
      _ = ∑ x : (ZMod p)ˣ, (∑ n ∈ Icc 1 k, (n : ZMod p) ^ t * (x : ZMod p) ^ n) ^ s := by
        refine sum_congr rfl fun x _ => ?_
        rw [sum_pow']
        simp only [tuples, weight, prod_mul_distrib, prod_pow, prod_pow_eq_pow_sum]
      _ = ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ s := by
        simp_rw [weighted_sum_eq_self hk ht hkcong hcases]
      _ = 0 := by
        simp [FiniteField.sum_pow_units, ZMod.card,
          Nat.not_dvd_of_pos_of_lt hs (show s < p - 1 by omega)]
  rw [sum_comm] at hmoment
  simp_rw [← mul_sum, FiniteField.sum_pow_units, ZMod.card] at hmoment
  apply (ZMod.natCast_eq_zero_iff _ p).1
  simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_prod]
  simp_rw [sum_filter]
  change ∑ j ∈ Icc 1 (k * s / (p - 1)),
    ∑ ω ∈ tuples, (if (∑ i, ω i) = j * (p - 1) then weight ω else 0) = 0
  rw [sum_comm, ← neg_eq_zero, ← sum_neg_distrib]
  refine (sum_congr rfl fun ω hω => ?_).trans hmoment
  have hcoord := Fintype.mem_piFinset.mp hω
  have hpos : 0 < ∑ i, ω i := sum_pos (fun i _ => (mem_Icc.mp (hcoord i)).1)
    ⟨⟨0, hs⟩, mem_univ _⟩
  have hle : ∑ i, ω i ≤ k * s := calc
    _ ≤ ∑ _ : Fin s, k := sum_le_sum fun i _ => (mem_Icc.mp (hcoord i)).2
    _ = _ := by simp [Nat.mul_comm]
  rw [sum_multiples hpos (by omega) hle]
  split <;> simp

/-- **Vishwakarma–Singh congruence for ordered partitions, linear case.** Let $p$ be an odd
prime and let $k, s$ be positive integers with $s \le p - 2$ and $k \equiv 1 \pmod{p(p-1)}$.
Let $\mu = \lfloor ks/(p - 1) \rfloor$. Then

$$\sum_{j=1}^{\mu} \sum_{\omega} \omega_1 \cdots \omega_s \equiv 0 \pmod{p},$$

where for each $j$ the inner sum runs over all $s$-tuples $\omega = (\omega_1, \dots, \omega_s)$
with entries in $\{1, \dots, k\}$ and $\omega_1 + \cdots + \omega_s = j(p - 1)$.

This is the case $t = 1$ of the source's Theorem 1. The source states the hypothesis
$s \not\equiv 0 \pmod{p}$ in place of $s \le p - 2$; with that hypothesis the claim fails, e.g.
for $p = 3$, $k = 7$, $s = 2$ the sum is $400 \equiv 1 \pmod{3}$.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Corollary 2
(`integers-2024-A12-cor-2`). -/
public theorem prime_dvd_sum_compositions_prod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {k s : ℕ} (hk : 0 < k) (hs : 0 < s) (hsp : s ≤ p - 2) (hkcong : k ≡ 1 [MOD p * (p - 1)]) :
    p ∣ ∑ j ∈ Finset.Icc 1 (k * s / (p - 1)),
      ∑ ω ∈ (Fintype.piFinset fun _ : Fin s => Finset.Icc 1 k).filter
          (fun ω => ∑ i, ω i = j * (p - 1)),
        ∏ i, ω i := by
  have hp₁ : 2 ≤ p - 1 := by
    have := hp.two_le
    omega
  have hnot : ¬ (p - 1) ∣ (1 : ℕ) := by
    intro hdiv
    have := Nat.dvd_one.mp hdiv
    omega
  simpa only [pow_one] using
    prime_dvd_sum_compositions_prod_pow (t := 1) hp hp2 hk hs hsp Nat.zero_lt_one hkcong
      (fun hdiv => (hnot hdiv).elim)

end MetaMathlibExt
