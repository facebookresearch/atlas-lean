/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.DoldSequence

@[expose] public section

namespace MetaMathlibExt

section

/-- **Binomial-power sequences.** For natural numbers $r$, $s$ and $n$, the binomial-power number
$A_{r,s}(n)$ is the natural number

$$A_{r,s}(n) = \sum_{k=0}^{n} \binom{n}{k}^r \binom{n+k}{k}^s.$$

Special cases include the central Delannoy numbers ($r = s = 1$), the Apéry numbers
($r = s = 2$) and the Franel numbers of order $r$ ($s = 0$).

Source: Geng-Rui Zhang, "Realizability of Some Combinatorial Sequences,"
Journal of Integer Sequences 27 (2024), Article 24.3.3, Theorem
(label Thm1.13), lines 143–144,
https://cs.uwaterloo.ca/journals/JIS/VOL27/Zhang/zhang9.tex
with `A(n,r,s)` at lines 120–122 (label Def1.5) and realizability at
lines 86–93 (label Def1.1). -/
def binomialPowerSeq (r s n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k) ^ r * (Nat.choose (n + k) k) ^ s

/-- **Dold realizable sequences.** An integer sequence $(a(n))_{n \ge 0}$ is Dold realizable when,
for every integer $n \ge 1$, the Möbius transform $\sum_{d \mid n} \mu(d)\, a(n/d)$ is divisible
by $n$ and non-negative, where $\mu$ is the Möbius function and $d$ runs over the positive
divisors of $n$.

The divisibility condition alone is the classical Dold condition.

Source: the repository's trace-side characterization is `MetaMathlibExt.IsDoldSequence`
(Wójcik, Lemma 3). The equivalence between the two forms is not formalized here. -/
def doldRealizable (a : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, 0 < n →
    (n : ℤ) ∣ ∑ d ∈ Nat.divisors n,
      (⇑ArithmeticFunction.moebius d) * a (n / d) ∧
    0 ≤ ∑ d ∈ Nat.divisors n,
      (⇑ArithmeticFunction.moebius d) * a (n / d)

/-- **Dold realizable sequences satisfy the Dold congruences.** If an integer sequence
$(a(n))_{n \ge 0}$ is Dold realizable, then for every integer $n \ge 1$, $n$ divides
$\sum_{d \mid n} \mu(d)\, a(n/d)$, where $\mu$ is the Möbius function and $d$ runs over the
positive divisors of $n$. -/
theorem doldRealizable_dvd {a : ℕ → ℤ} (h : doldRealizable a) (n : ℕ)
    (hn : 0 < n) :
    (n : ℤ) ∣ ∑ d ∈ Nat.divisors n,
      (⇑ArithmeticFunction.moebius d) * a (n / d) :=
  (h n hn).1

/-- **The Möbius transform of a Dold realizable sequence is non-negative.** If an integer sequence
$(a(n))_{n \ge 0}$ is Dold realizable, then for every integer $n \ge 1$,
$\sum_{d \mid n} \mu(d)\, a(n/d) \ge 0$, where $\mu$ is the Möbius function and $d$ runs over
the positive divisors of $n$. -/
theorem doldRealizable_nonneg {a : ℕ → ℤ} (h : doldRealizable a) (n : ℕ)
    (hn : 0 < n) :
    0 ≤ ∑ d ∈ Nat.divisors n,
      (⇑ArithmeticFunction.moebius d) * a (n / d) :=
  (h n hn).2

/-- **Criterion for Dold realizability.** Let $(a(n))_{n \ge 0}$ be an integer sequence and let
$\mu$ be the Möbius function. If for every integer $n \ge 1$ the sum
$\sum_{d \mid n} \mu(d)\, a(n/d)$ over the positive divisors $d$ of $n$ is divisible by $n$, and
for every integer $n \ge 1$ this sum is non-negative, then $a$ is Dold realizable. -/
theorem doldRealizable_of_dvd_and_nonneg {a : ℕ → ℤ}
    (hdvd : ∀ n : ℕ, 0 < n →
      (n : ℤ) ∣ ∑ d ∈ Nat.divisors n,
        (⇑ArithmeticFunction.moebius d) * a (n / d))
    (hnn : ∀ n : ℕ, 0 < n →
      0 ≤ ∑ d ∈ Nat.divisors n,
        (⇑ArithmeticFunction.moebius d) * a (n / d)) :
    doldRealizable a :=
  fun n hn => ⟨hdvd n hn, hnn n hn⟩

private theorem binomialPowerSeq_one_zero (n : ℕ) : binomialPowerSeq 1 0 n = 2 ^ n := by
  unfold binomialPowerSeq
  have h : ∀ k : ℕ,
      (Nat.choose n k) ^ 1 * (Nat.choose (n + k) k) ^ 0 = Nat.choose n k := by
    intro k
    simp
  simp_rw [h]
  exact Nat.sum_range_choose n

private theorem binomialPowerSeq_term_ge_choose (r s n k : ℕ) (hr : 0 < r) (_hkn : k ≤ n) :
    Nat.choose n k ≤ (Nat.choose n k) ^ r * (Nat.choose (n + k) k) ^ s := by
  have hCpos : 0 < Nat.choose (n + k) k := Nat.choose_pos (Nat.le_add_left k n)
  have h1 : Nat.choose n k ≤ (Nat.choose n k) ^ r :=
    Nat.le_self_pow (ne_of_gt hr) _
  have h2 : 1 ≤ (Nat.choose (n + k) k) ^ s := Nat.one_le_pow s _ hCpos
  calc Nat.choose n k ≤ (Nat.choose n k) ^ r := h1
    _ = (Nat.choose n k) ^ r * 1 := (Nat.mul_one _).symm
    _ ≤ (Nat.choose n k) ^ r * (Nat.choose (n + k) k) ^ s :=
        Nat.mul_le_mul_left _ h2

private theorem binomialPowerSeq_ge_two_pow (r s n : ℕ) (hr : 0 < r) :
    2 ^ n ≤ binomialPowerSeq r s n := by
  unfold binomialPowerSeq
  rw [← Nat.sum_range_choose n]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_range] at hk
  exact binomialPowerSeq_term_ge_choose r s n k hr (Nat.lt_succ_iff.mp hk)

private theorem binomialPowerSeq_pos (r s n : ℕ) (hr : 0 < r) :
    0 < binomialPowerSeq r s n :=
  lt_of_lt_of_le (Nat.pow_pos (by norm_num : 0 < 2)) (binomialPowerSeq_ge_two_pow r s n hr)

private theorem binomialPowerSeq_zero (r s : ℕ) : binomialPowerSeq r s 0 = 1 := by
  simp [binomialPowerSeq]

private theorem add_pow_ge_add_pow (a b t : ℕ) :
    a ^ (t + 1) + b ^ (t + 1) ≤ (a + b) ^ (t + 1) := by
  have ha : a ^ t ≤ (a + b) ^ t :=
    Nat.pow_le_pow_left (Nat.le_add_right a b) t
  have hb : b ^ t ≤ (a + b) ^ t :=
    Nat.pow_le_pow_left (Nat.le_add_left b a) t
  have e : (a + b) ^ (t + 1) = a * (a + b) ^ t + b * (a + b) ^ t := by
    rw [pow_succ', Nat.add_mul]
  rw [e]
  have h1 : a ^ (t + 1) ≤ a * (a + b) ^ t := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left a ha
  have h2 : b ^ (t + 1) ≤ b * (a + b) ^ t := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left b hb
  exact Nat.add_le_add h1 h2

private theorem choose_shift_le (n j : ℕ) :
    Nat.choose (n + j) j ≤ Nat.choose (n + 1 + j) (j + 1) := by
  have h1 : n + j = j + n := Nat.add_comm n j
  have h2 : n + 1 + j = (j + 1) + n := by omega
  have e1 : Nat.choose (n + j) j = Nat.choose (n + j) n :=
    Nat.choose_symm_of_eq_add h1
  have e2 : Nat.choose (n + 1 + j) (j + 1) = Nat.choose (n + 1 + j) n :=
    Nat.choose_symm_of_eq_add h2
  rw [e1, e2]
  exact Nat.choose_le_choose n (by omega)

private theorem binomialPowerSeq_term_zero (r s n : ℕ) (hr : 0 < r) :
    (Nat.choose n (n + 1)) ^ r * (Nat.choose (n + (n + 1)) (n + 1)) ^ s = 0 := by
  have h0 : Nat.choose n (n + 1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)
  have hrne : r ≠ 0 := ne_of_gt hr
  simp only [h0, zero_pow hrne, zero_mul]

private theorem binomialPowerSeq_term0_eq_one (r s n : ℕ) :
    (Nat.choose n 0) ^ r * (Nat.choose (n + 0) 0) ^ s = 1 := by
  simp only [Nat.choose_zero_right, Nat.add_zero, one_pow, mul_one]

private theorem binomialPowerSeq_succ_term_ge (r s n j : ℕ) (hr : 0 < r) :
    (Nat.choose n j) ^ r * (Nat.choose (n + j) j) ^ s +
        (Nat.choose n (j + 1)) ^ r * (Nat.choose (n + (j + 1)) (j + 1)) ^ s ≤
      (Nat.choose (n + 1) (j + 1)) ^ r *
        (Nat.choose (n + 1 + (j + 1)) (j + 1)) ^ s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (ne_of_gt hr)
  have hpascal : Nat.choose (n + 1) (j + 1)
      = Nat.choose n j + Nat.choose n (j + 1) :=
    Nat.choose_succ_succ' n j
  have hpow : (Nat.choose n j) ^ (t + 1) + (Nat.choose n (j + 1)) ^ (t + 1)
      ≤ (Nat.choose (n + 1) (j + 1)) ^ (t + 1) := by
    rw [hpascal]
    exact add_pow_ge_add_pow _ _ t
  have hle1 : Nat.choose (n + j) j ≤ Nat.choose (n + 1 + (j + 1)) (j + 1) := by
    have h1 : Nat.choose (n + j) j ≤ Nat.choose (n + 1 + j) (j + 1) :=
      choose_shift_le n j
    have h2 : Nat.choose (n + 1 + j) (j + 1)
        ≤ Nat.choose (n + 1 + (j + 1)) (j + 1) :=
      Nat.choose_le_choose (j + 1) (by omega)
    exact le_trans h1 h2
  have hle2 : Nat.choose (n + (j + 1)) (j + 1)
      ≤ Nat.choose (n + 1 + (j + 1)) (j + 1) :=
    Nat.choose_le_choose (j + 1) (by omega)
  have hs1 : (Nat.choose (n + j) j) ^ s
      ≤ (Nat.choose (n + 1 + (j + 1)) (j + 1)) ^ s :=
    Nat.pow_le_pow_left hle1 s
  have hs2 : (Nat.choose (n + (j + 1)) (j + 1)) ^ s
      ≤ (Nat.choose (n + 1 + (j + 1)) (j + 1)) ^ s :=
    Nat.pow_le_pow_left hle2 s
  have h1 : (Nat.choose n j) ^ (t + 1) * (Nat.choose (n + j) j) ^ s
      ≤ (Nat.choose n j) ^ (t + 1) *
        (Nat.choose (n + 1 + (j + 1)) (j + 1)) ^ s :=
    Nat.mul_le_mul_left _ hs1
  have h2 : (Nat.choose n (j + 1)) ^ (t + 1) *
        (Nat.choose (n + (j + 1)) (j + 1)) ^ s
      ≤ (Nat.choose n (j + 1)) ^ (t + 1) *
        (Nat.choose (n + 1 + (j + 1)) (j + 1)) ^ s :=
    Nat.mul_le_mul_left _ hs2
  calc (Nat.choose n j) ^ (t + 1) * (Nat.choose (n + j) j) ^ s +
          (Nat.choose n (j + 1)) ^ (t + 1) *
            (Nat.choose (n + (j + 1)) (j + 1)) ^ s
        ≤ (Nat.choose n j) ^ (t + 1) *
            (Nat.choose (n + 1 + (j + 1)) (j + 1)) ^ s +
            (Nat.choose n (j + 1)) ^ (t + 1) *
              (Nat.choose (n + 1 + (j + 1)) (j + 1)) ^ s :=
          Nat.add_le_add h1 h2
      _ = ((Nat.choose n j) ^ (t + 1) + (Nat.choose n (j + 1)) ^ (t + 1)) *
          (Nat.choose (n + 1 + (j + 1)) (j + 1)) ^ s :=
          (Nat.add_mul _ _ _).symm
      _ ≤ (Nat.choose (n + 1) (j + 1)) ^ (t + 1) *
          (Nat.choose (n + 1 + (j + 1)) (j + 1)) ^ s :=
          Nat.mul_le_mul_right _ hpow

private theorem binomialPowerSeq_double (r s n : ℕ) (hr : 0 < r) :
    2 * binomialPowerSeq r s n ≤ binomialPowerSeq r s (n + 1) := by
  have hF0 : (Nat.choose n 0) ^ r * (Nat.choose (n + 0) 0) ^ s = 1 :=
    binomialPowerSeq_term0_eq_one r s n
  have hG0 : (Nat.choose (n + 1) 0) ^ r * (Nat.choose (n + 1 + 0) 0) ^ s = 1 :=
    binomialPowerSeq_term0_eq_one r s (n + 1)
  have hFn1 : (Nat.choose n (n + 1)) ^ r *
      (Nat.choose (n + (n + 1)) (n + 1)) ^ s = 0 :=
    binomialPowerSeq_term_zero r s n hr
  have hterm : ∀ j ∈ Finset.range (n + 1),
      (Nat.choose n j) ^ r * (Nat.choose (n + j) j) ^ s +
          (Nat.choose n (j + 1)) ^ r *
            (Nat.choose (n + (j + 1)) (j + 1)) ^ s ≤
        (Nat.choose (n + 1) (j + 1)) ^ r *
          (Nat.choose (n + 1 + (j + 1)) (j + 1)) ^ s := by
    intro j _
    exact binomialPowerSeq_succ_term_ge r s n j hr
  have hsumle : (∑ j ∈ Finset.range (n + 1),
        ((Nat.choose n j) ^ r * (Nat.choose (n + j) j) ^ s +
          (Nat.choose n (j + 1)) ^ r *
            (Nat.choose (n + (j + 1)) (j + 1)) ^ s)) ≤
      ∑ j ∈ Finset.range (n + 1),
        ((Nat.choose (n + 1) (j + 1)) ^ r *
          (Nat.choose (n + 1 + (j + 1)) (j + 1)) ^ s) :=
    Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsumle
  have hsplitG : (∑ k ∈ Finset.range (n + 1 + 1),
        ((Nat.choose (n + 1) k) ^ r * (Nat.choose (n + 1 + k) k) ^ s)) =
      (∑ j ∈ Finset.range (n + 1),
        ((Nat.choose (n + 1) (j + 1)) ^ r *
          (Nat.choose (n + 1 + (j + 1)) (j + 1)) ^ s)) +
        ((Nat.choose (n + 1) 0) ^ r * (Nat.choose (n + 1 + 0) 0) ^ s) :=
    Finset.sum_range_succ' _ (n + 1)
  have hsplitF : (∑ k ∈ Finset.range (n + 1 + 1),
        ((Nat.choose n k) ^ r * (Nat.choose (n + k) k) ^ s)) =
      (∑ j ∈ Finset.range (n + 1),
        ((Nat.choose n (j + 1)) ^ r *
          (Nat.choose (n + (j + 1)) (j + 1)) ^ s)) +
        ((Nat.choose n 0) ^ r * (Nat.choose (n + 0) 0) ^ s) :=
    Finset.sum_range_succ' _ (n + 1)
  have hextF : (∑ k ∈ Finset.range (n + 1 + 1),
        ((Nat.choose n k) ^ r * (Nat.choose (n + k) k) ^ s)) =
      (∑ k ∈ Finset.range (n + 1),
        ((Nat.choose n k) ^ r * (Nat.choose (n + k) k) ^ s)) +
        ((Nat.choose n (n + 1)) ^ r *
          (Nat.choose (n + (n + 1)) (n + 1)) ^ s) :=
    Finset.sum_range_succ _ (n + 1)
  rw [hG0] at hsplitG
  rw [hF0] at hsplitF
  rw [hFn1] at hextF
  simp only [add_zero] at hsplitF hextF
  have hSeq : (∑ j ∈ Finset.range (n + 1),
        ((Nat.choose n (j + 1)) ^ r *
          (Nat.choose (n + (j + 1)) (j + 1)) ^ s)) + 1 =
      ∑ k ∈ Finset.range (n + 1),
        ((Nat.choose n k) ^ r * (Nat.choose (n + k) k) ^ s) := by
    omega
  unfold binomialPowerSeq
  omega

private theorem binomialPowerSeq_sum_range_le (r s : ℕ) (hr : 0 < r) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), binomialPowerSeq r s k
      ≤ 2 * binomialPowerSeq r s n := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    omega
  | succ n ih =>
    have hdouble := binomialPowerSeq_double r s n hr
    have hsplit := Finset.sum_range_succ
      (fun k => binomialPowerSeq r s k) (n + 1)
    omega

private theorem binomialPowerSeq_sum_range_lt (r s : ℕ) (hr : 0 < r) (n : ℕ)
    (hn : 0 < n) :
    ∑ k ∈ Finset.range n, binomialPowerSeq r s k
      ≤ binomialPowerSeq r s n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (ne_of_gt hn)
  have hle := binomialPowerSeq_sum_range_le r s hr m
  have hdouble := binomialPowerSeq_double r s m hr
  omega

private theorem div_image_inj (n : ℕ) (hn : 0 < n) :
    ∀ d1 ∈ (Nat.divisors n).erase 1, ∀ d2 ∈ (Nat.divisors n).erase 1,
      n / d1 = n / d2 → d1 = d2 := by
  intro d1 hd1 d2 hd2 heq
  have hmem1 := Finset.mem_of_mem_erase hd1
  have hmem2 := Finset.mem_of_mem_erase hd2
  have hdvd1 := Nat.dvd_of_mem_divisors hmem1
  have hdvd2 := Nat.dvd_of_mem_divisors hmem2
  obtain ⟨c1, hc1⟩ := hdvd1
  obtain ⟨c2, hc2⟩ := hdvd2
  have hd1pos : 0 < d1 := by
    rcases Nat.eq_zero_or_pos d1 with rfl | hpos
    · simp_all
    · exact hpos
  have hd2pos : 0 < d2 := by
    rcases Nat.eq_zero_or_pos d2 with rfl | hpos
    · simp_all
    · exact hpos
  have e1 : n / d1 = c1 := by
    rw [hc1, Nat.mul_div_cancel_left _ hd1pos]
  have e2 : n / d2 = c2 := by
    rw [hc2, Nat.mul_div_cancel_left _ hd2pos]
  rw [e1, e2] at heq
  have hc1pos : 0 < c1 := by
    rcases Nat.eq_zero_or_pos c1 with rfl | hpos
    · rw [hc1] at hn
      simp at hn
    · exact hpos
  have hmul : d1 * c1 = d2 * c1 := by
    rw [← hc1, heq]
    exact hc2
  exact Nat.mul_right_cancel hc1pos hmul

private theorem div_mem_range_of_erase (n d : ℕ) (hn : 0 < n)
    (hd : d ∈ (Nat.divisors n).erase 1) : n / d < n := by
  have hmem := Finset.mem_of_mem_erase hd
  have hdvd := Nat.dvd_of_mem_divisors hmem
  have hdne : d ≠ 1 := Finset.ne_of_mem_erase hd
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · simp_all
    · exact hpos
  have hd2 : 1 < d := by omega
  exact Nat.div_lt_self hn hd2

private theorem div_ne_zero_of_erase (n d : ℕ) (hn : 0 < n)
    (hd : d ∈ (Nat.divisors n).erase 1) : n / d ≠ 0 := by
  have hmem := Finset.mem_of_mem_erase hd
  have hdvd := Nat.dvd_of_mem_divisors hmem
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · simp_all
    · exact hpos
  have hle : d ≤ n := Nat.le_of_dvd hn hdvd
  have hpos : 0 < n / d := Nat.div_pos hle hdpos
  omega

private theorem binomialPowerSeq_erase_sum_le (r s n : ℕ) (hr : 0 < r)
    (hn : 0 < n) :
    (∑ d ∈ (Nat.divisors n).erase 1, binomialPowerSeq r s (n / d)) + 1
      ≤ binomialPowerSeq r s n := by
  have hinj := div_image_inj n hn
  have himage : (∑ d ∈ (Nat.divisors n).erase 1,
        binomialPowerSeq r s (n / d)) =
      ∑ e ∈ ((Nat.divisors n).erase 1).image (fun d => n / d),
        binomialPowerSeq r s e := by
    exact (Finset.sum_image (f := fun e => binomialPowerSeq r s e) hinj).symm
  have hsub : ((Nat.divisors n).erase 1).image (fun d => n / d)
      ⊆ (Finset.range n).erase 0 := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨d, hd, rfl⟩ := he
    rw [Finset.mem_erase]
    constructor
    · exact div_ne_zero_of_erase n d hn hd
    · exact Finset.mem_range.mpr (div_mem_range_of_erase n d hn hd)
  have hle1 : (∑ e ∈ ((Nat.divisors n).erase 1).image (fun d => n / d),
        binomialPowerSeq r s e) ≤
      ∑ e ∈ (Finset.range n).erase 0, binomialPowerSeq r s e :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => Nat.zero_le _)
  have h0mem : 0 ∈ Finset.range n := Finset.mem_range.mpr hn
  have hA0 : binomialPowerSeq r s 0 = 1 := binomialPowerSeq_zero r s
  have hdecomp := Finset.add_sum_erase (Finset.range n)
    (fun e => binomialPowerSeq r s e) h0mem
  rw [hA0] at hdecomp
  have hle2 : ∑ k ∈ Finset.range n, binomialPowerSeq r s k
      ≤ binomialPowerSeq r s n :=
    binomialPowerSeq_sum_range_lt r s hr n hn
  omega

private theorem moebius_ge_neg_one (d : ℕ) :
    -1 ≤ (⇑ArithmeticFunction.moebius d) := by
  have h := ArithmeticFunction.moebius_eq_or d
  rcases h with h | h | h
  · rw [h]
    omega
  · rw [h]
    omega
  · rw [h]

private theorem prod_Icc_one_eq_factorial (K : ℕ) :
    ∏ i ∈ Finset.Icc 1 K, i = Nat.factorial K := by
  induction K with
  | zero =>
    simp only [Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 from by omega)]
    simp
  | succ K ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ K + 1) _]
    rw [ih, Nat.factorial_succ, mul_comm]

private theorem prod_Icc_add_mul_factorial (N K : ℕ) :
    (∏ i ∈ Finset.Icc 1 K, (N + i)) * Nat.factorial N
      = Nat.factorial (N + K) := by
  induction K with
  | zero =>
    simp only [Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 from by omega)]
    simp
  | succ K ih =>
    have hprod : (∏ i ∈ Finset.Icc 1 (K + 1), (N + i)) =
        (∏ i ∈ Finset.Icc 1 K, (N + i)) * (N + (K + 1)) :=
      Finset.prod_Icc_succ_top (by omega : 1 ≤ K + 1) _
    have hNK : N + (K + 1) = (N + K) + 1 := by omega
    rw [hprod, hNK]
    have hfact : Nat.factorial (N + K) * ((N + K) + 1)
        = Nat.factorial ((N + K) + 1) := by
      rw [mul_comm]
      exact (Nat.factorial_succ (N + K)).symm
    calc (∏ i ∈ Finset.Icc 1 K, (N + i)) * ((N + K) + 1)
          * Nat.factorial N
        = (∏ i ∈ Finset.Icc 1 K, (N + i)) * Nat.factorial N
          * ((N + K) + 1) := by
          rw [mul_assoc, mul_comm ((N + K) + 1) (Nat.factorial N)]
          rw [← mul_assoc]
      _ = Nat.factorial (N + K) * ((N + K) + 1) := by rw [ih]
      _ = Nat.factorial ((N + K) + 1) := hfact

private theorem image_mul_eq_filter (p J : ℕ) (hp : 0 < p) :
    Finset.image (fun t => p * t) (Finset.Icc 1 J)
      = (Finset.Icc 1 (p * J)).filter (fun i => p ∣ i) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_filter]
  constructor
  · rintro ⟨t, ⟨h1t, htJ⟩, rfl⟩
    constructor
    · constructor
      · calc 1 ≤ p * 1 := by
              rw [mul_one]
              exact hp
          _ ≤ p * t := by
              exact Nat.mul_le_mul_left p h1t
      · exact Nat.mul_le_mul_left p htJ
    · exact Dvd.intro t rfl
  · rintro ⟨⟨h1i, hiJ⟩, ⟨t, rfl⟩⟩
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with rfl | hpos
      · simp at h1i
      · exact hpos
    have ht1 : 1 ≤ t := htpos
    have htJ : t ≤ J := by
      have hle : p * t ≤ p * J := hiJ
      exact Nat.le_of_mul_le_mul_left hle hp
    exact ⟨t, ⟨ht1, htJ⟩, rfl⟩

private theorem prod_filter_dvd_eq (p J : ℕ) (hp : 0 < p) :
    ∏ i ∈ (Finset.Icc 1 (p * J)).filter (fun i => p ∣ i), i
      = p ^ J * ∏ t ∈ Finset.Icc 1 J, t := by
  have himg := image_mul_eq_filter p J hp
  have hinj : ∀ x ∈ Finset.Icc 1 J, ∀ y ∈ Finset.Icc 1 J,
      p * x = p * y → x = y := by
    intro x _ y _ h
    exact Nat.mul_left_cancel hp h
  have hprod : (∏ i ∈ Finset.image (fun t => p * t) (Finset.Icc 1 J), i)
      = ∏ t ∈ Finset.Icc 1 J, p * t := by
    exact Finset.prod_image hinj
  rw [himg] at hprod
  rw [hprod]
  rw [Finset.prod_mul_distrib]
  have hcard : (Finset.Icc 1 J).card = J := by
    rw [Nat.card_Icc]
    omega
  rw [Finset.prod_const, hcard]

private theorem prod_filter_add_eq (p J M : ℕ) (hp : 0 < p) :
    ∏ i ∈ (Finset.Icc 1 (p * J)).filter (fun i => p ∣ i), (p * M + i)
      = p ^ J * ∏ t ∈ Finset.Icc 1 J, (M + t) := by
  have himg := image_mul_eq_filter p J hp
  have hinj : ∀ x ∈ Finset.Icc 1 J, ∀ y ∈ Finset.Icc 1 J,
      p * x = p * y → x = y := by
    intro x _ y _ h
    exact Nat.mul_left_cancel hp h
  have hprod : (∏ i ∈ Finset.image (fun t => p * t) (Finset.Icc 1 J),
        (p * M + i))
      = ∏ t ∈ Finset.Icc 1 J, (p * M + p * t) := by
    exact Finset.prod_image hinj
  rw [himg] at hprod
  rw [hprod]
  have heq : ∀ t ∈ Finset.Icc 1 J, p * M + p * t = p * (M + t) := by
    intro t _
    rw [Nat.mul_add]
  rw [Finset.prod_congr rfl heq]
  rw [Finset.prod_mul_distrib]
  have hcard : (Finset.Icc 1 J).card = J := by
    rw [Nat.card_Icc]
    omega
  rw [Finset.prod_const, hcard]

private theorem choose_mul_prod_Icc (N K : ℕ) :
    Nat.choose (N + K) K * (∏ i ∈ Finset.Icc 1 K, i)
      = ∏ i ∈ Finset.Icc 1 K, (N + i) := by
  have h1 := Nat.add_choose_mul_factorial_mul_factorial N K
  have h2 := prod_Icc_add_mul_factorial N K
  have h3 := prod_Icc_one_eq_factorial K
  have hpos : 0 < Nat.factorial N := Nat.factorial_pos N
  have hmul : (Nat.choose (N + K) K * (∏ i ∈ Finset.Icc 1 K, i))
      * Nat.factorial N
      = (∏ i ∈ Finset.Icc 1 K, (N + i)) * Nat.factorial N := by
    rw [mul_assoc, h3]
    have hcomm : Nat.factorial K * Nat.factorial N
        = Nat.factorial N * Nat.factorial K := by rw [mul_comm]
    rw [hcomm, ← mul_assoc]
    rw [h1]
    exact h2.symm
  exact Nat.mul_right_cancel hpos hmul

private theorem prod_unit_congr_add (p N K k : ℕ) (hNdiv : p ^ k ∣ N) :
    (((∏ i ∈ (Finset.Icc 1 K).filter (fun i => ¬ p ∣ i), (N + i) : ℕ))
      : ZMod (p ^ k))
      = (((∏ i ∈ (Finset.Icc 1 K).filter (fun i => ¬ p ∣ i), i : ℕ))
        : ZMod (p ^ k)) := by
  have hN0 : ((N : ℕ) : ZMod (p ^ k)) = 0 :=
    (ZMod.natCast_eq_zero_iff N (p ^ k)).mpr hNdiv
  have hterm : ∀ i ∈ (Finset.Icc 1 K).filter (fun i => ¬ p ∣ i),
      (((N + i : ℕ)) : ZMod (p ^ k)) = ((i : ℕ) : ZMod (p ^ k)) := by
    intro i _
    rw [Nat.cast_add, hN0, zero_add]
  have hprod : (∏ i ∈ (Finset.Icc 1 K).filter (fun i => ¬ p ∣ i),
        (((N + i : ℕ)) : ZMod (p ^ k)))
      = ∏ i ∈ (Finset.Icc 1 K).filter (fun i => ¬ p ∣ i),
        ((i : ℕ) : ZMod (p ^ k)) :=
    Finset.prod_congr rfl hterm
  simp only [Nat.cast_prod] at hprod ⊢
  exact hprod

private theorem coprime_prod_filter (p K k : ℕ) [Fact (Nat.Prime p)] :
    Nat.Coprime
      (∏ i ∈ (Finset.Icc 1 K).filter (fun i => ¬ p ∣ i), i) (p ^ k) := by
  have hp : Nat.Prime p := Fact.out
  rw [Nat.coprime_prod_left_iff]
  intro i hi
  have hndvd : ¬ p ∣ i := (Finset.mem_filter.mp hi).2
  have h1 : Nat.Coprime p i := (hp.coprime_iff_not_dvd).mpr hndvd
  have h2 : Nat.Coprime i p := h1.symm
  exact h2.pow_right k

private theorem choose_add_unit_eq (p N M K J : ℕ) (hp : 0 < p)
    (hN : N = p * M) (hK : K = p * J) :
    Nat.choose (N + K) K *
        (∏ i ∈ (Finset.Icc 1 K).filter (fun i => ¬ p ∣ i), i)
      = Nat.choose (M + J) J *
        (∏ i ∈ (Finset.Icc 1 K).filter (fun i => ¬ p ∣ i), (N + i)) := by
  have hCD1 := choose_mul_prod_Icc N K
  have hCD2 := choose_mul_prod_Icc M J
  have hsplitP := Finset.prod_filter_mul_prod_filter_not
    (Finset.Icc 1 K) (fun i => p ∣ i) (fun i => N + i)
  have hsplitD := Finset.prod_filter_mul_prod_filter_not
    (Finset.Icc 1 K) (fun i => p ∣ i) (fun i => i)
  have hDp : ∏ i ∈ (Finset.Icc 1 K).filter (fun i => p ∣ i), i
      = p ^ J * ∏ t ∈ Finset.Icc 1 J, t := by
    rw [hK]
    exact prod_filter_dvd_eq p J hp
  have hPp : ∏ i ∈ (Finset.Icc 1 K).filter (fun i => p ∣ i), (N + i)
      = p ^ J * ∏ t ∈ Finset.Icc 1 J, (M + t) := by
    rw [hK, hN]
    exact prod_filter_add_eq p J M hp
  have hposP : 0 < p ^ J := Nat.pow_pos hp
  have hposE : 0 < ∏ t ∈ Finset.Icc 1 J, t := by
    apply Finset.prod_pos
    intro t ht
    have h1t : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    omega
  have hposPE : 0 < p ^ J * ∏ t ∈ Finset.Icc 1 J, t :=
    Nat.mul_pos hposP hposE
  have heq : (p ^ J * ∏ t ∈ Finset.Icc 1 J, t) *
        (Nat.choose (N + K) K *
          ∏ i ∈ (Finset.Icc 1 K).filter (fun i => ¬ p ∣ i), i)
      = (p ^ J * ∏ t ∈ Finset.Icc 1 J, t) *
        (Nat.choose (M + J) J *
          ∏ i ∈ (Finset.Icc 1 K).filter (fun i => ¬ p ∣ i), (N + i)) := by
    have e1 : Nat.choose (N + K) K *
          (∏ i ∈ Finset.Icc 1 K, i)
        = ∏ i ∈ Finset.Icc 1 K, (N + i) := hCD1
    rw [← hsplitD, ← hsplitP] at e1
    rw [hDp, hPp] at e1
    have e2 : ∏ t ∈ Finset.Icc 1 J, (M + t)
        = Nat.choose (M + J) J * ∏ t ∈ Finset.Icc 1 J, t := by
      exact hCD2.symm
    rw [e2] at e1
    ring_nf at e1 ⊢
    exact e1
  exact Nat.mul_left_cancel hposPE heq

private theorem prod_range_add_one_eq_factorial (K : ℕ) :
    ∏ t ∈ Finset.range K, (t + 1) = Nat.factorial K := by
  induction K with
  | zero =>
    simp
  | succ K ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ, mul_comm]

private theorem prod_range_sub_mul_factorial (N K : ℕ) (hKN : K ≤ N) :
    (∏ t ∈ Finset.range K, (N - t)) * Nat.factorial (N - K)
      = Nat.factorial N := by
  induction K generalizing N with
  | zero =>
    simp
  | succ K ih =>
    have hKN' : K ≤ N := by omega
    have hsucc_le : K + 1 ≤ N := hKN
    have hprod : (∏ t ∈ Finset.range (K + 1), (N - t))
        = (∏ t ∈ Finset.range K, (N - t)) * (N - K) := by
      rw [Finset.prod_range_succ]
    rw [hprod]
    have hsub : N - (K + 1) + 1 = N - K := by omega
    have hfact : Nat.factorial (N - K)
        = (N - K) * Nat.factorial (N - (K + 1)) := by
      rw [← hsub, Nat.factorial_succ]
    have ih' := ih N hKN'
    have hcalc : (∏ t ∈ Finset.range K, (N - t)) * (N - K)
        * Nat.factorial (N - (K + 1))
        = (∏ t ∈ Finset.range K, (N - t))
          * Nat.factorial (N - K) := by
      rw [hfact]
      ring
    rw [hcalc, ih']

private theorem image_range_mul_eq_filter (p J : ℕ) (hp : 0 < p) :
    Finset.image (fun s => p * s) (Finset.range J)
      = (Finset.range (p * J)).filter (fun t => p ∣ t) := by
  ext t
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter]
  constructor
  · rintro ⟨s, hs, rfl⟩
    constructor
    · exact (Nat.mul_lt_mul_left hp).mpr hs
    · exact Dvd.intro s rfl
  · rintro ⟨ht, ⟨s, rfl⟩⟩
    have hsJ : s < J := (Nat.mul_lt_mul_left hp).mp ht
    exact ⟨s, hsJ, rfl⟩

private theorem prod_range_filter_sub_eq (p J M : ℕ) (hp : 0 < p) :
    ∏ t ∈ (Finset.range (p * J)).filter (fun t => p ∣ t), (p * M - t)
      = p ^ J * ∏ s ∈ Finset.range J, (M - s) := by
  have himg := image_range_mul_eq_filter p J hp
  have hinj : ∀ x ∈ Finset.range J, ∀ y ∈ Finset.range J,
      p * x = p * y → x = y := by
    intro x _ y _ h
    exact Nat.mul_left_cancel hp h
  have hprod : (∏ t ∈ Finset.image (fun s => p * s) (Finset.range J),
        (p * M - t))
      = ∏ s ∈ Finset.range J, (p * M - p * s) := by
    exact Finset.prod_image hinj
  rw [himg] at hprod
  rw [hprod]
  have heq : ∀ s ∈ Finset.range J, p * M - p * s = p * (M - s) := by
    intro s hs
    rw [← Nat.mul_sub]
  rw [Finset.prod_congr rfl heq]
  rw [Finset.prod_mul_distrib]
  have hcard : (Finset.range J).card = J := Finset.card_range J
  rw [Finset.prod_const, hcard]

private theorem prod_range_succ_filter_eq (p K : ℕ) :
    ∏ t ∈ (Finset.range K).filter (fun t => p ∣ t + 1), (t + 1)
      = ∏ i ∈ (Finset.Icc 1 K).filter (fun i => p ∣ i), i := by
  apply Finset.prod_bij (fun t _ => t + 1)
  · intro t ht
    have hmem := Finset.mem_filter.mp ht
    have htK : t < K := Finset.mem_range.mp hmem.1
    have hdvd := hmem.2
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_Icc]
      constructor
      · omega
      · omega
    · exact hdvd
  · intro t1 ht1 t2 ht2 h12
    omega
  · intro i hi
    have hmem := Finset.mem_filter.mp hi
    have hIcc := Finset.mem_Icc.mp hmem.1
    have hdvd := hmem.2
    have hi1 : 1 ≤ i := hIcc.1
    refine ⟨i - 1, ?_, by omega⟩
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_range]
      omega
    · have e : i - 1 + 1 = i := Nat.sub_add_cancel hi1
      rw [e]
      exact hdvd
  · intro t ht
    rfl

private theorem prod_range_dvd_succ_eq (p J : ℕ) (hp : 0 < p) :
    ∏ t ∈ (Finset.range (p * J)).filter (fun t => p ∣ t + 1), (t + 1)
      = p ^ J * ∏ s ∈ Finset.range J, (s + 1) := by
  have h1 := prod_range_succ_filter_eq p (p * J)
  have h2 := prod_filter_dvd_eq p J hp
  have h3 : (∏ t ∈ Finset.Icc 1 J, t)
      = ∏ s ∈ Finset.range J, (s + 1) := by
    rw [prod_Icc_one_eq_factorial, prod_range_add_one_eq_factorial]
  rw [h1, h2, h3]

private theorem filter_range_eq_filter_Icc (p K J : ℕ) (hK : K = p * J) :
    (Finset.range K).filter (fun t => ¬ p ∣ t)
      = (Finset.Icc 1 K).filter (fun i => ¬ p ∣ i) := by
  have hKdvd : p ∣ K := by
    rw [hK]
    exact dvd_mul_right p J
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨htK, hndvd⟩
    have htne : t ≠ 0 := by
      rintro rfl
      exact hndvd (dvd_zero p)
    constructor
    · constructor
      · omega
      · omega
    · exact hndvd
  · rintro ⟨⟨h1t, htK⟩, hndvd⟩
    have htneK : t ≠ K := by
      rintro rfl
      exact hndvd hKdvd
    constructor
    · omega
    · exact hndvd

private theorem prod_range_notdvd_eq (p K : ℕ) :
    ∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t + 1), (t + 1)
      = ∏ i ∈ (Finset.Icc 1 K).filter (fun i => ¬ p ∣ i), i := by
  have hfullR := prod_range_add_one_eq_factorial K
  have hfullI := prod_Icc_one_eq_factorial K
  have hsplitR := Finset.prod_filter_mul_prod_filter_not
    (Finset.range K) (fun t => p ∣ t + 1) (fun t => t + 1)
  have hsplitI := Finset.prod_filter_mul_prod_filter_not
    (Finset.Icc 1 K) (fun i => p ∣ i) (fun i => i)
  have hp_eq := prod_range_succ_filter_eq p K
  have hpos : 0 < ∏ t ∈ (Finset.range K).filter
      (fun t => p ∣ t + 1), (t + 1) := by
    apply Finset.prod_pos
    intro t ht
    omega
  have heq : (∏ t ∈ (Finset.range K).filter
        (fun t => p ∣ t + 1), (t + 1))
        * (∏ t ∈ (Finset.range K).filter
          (fun t => ¬ p ∣ t + 1), (t + 1))
      = (∏ t ∈ (Finset.range K).filter
        (fun t => p ∣ t + 1), (t + 1))
        * (∏ i ∈ (Finset.Icc 1 K).filter (fun i => ¬ p ∣ i), i) := by
    have hfull : (∏ t ∈ Finset.range K, (t + 1))
        = ∏ i ∈ Finset.Icc 1 K, i := by
      rw [hfullR, hfullI]
    rw [← hsplitR, ← hsplitI] at hfull
    rw [hp_eq] at hfull
    rw [hp_eq]
    exact hfull
  exact Nat.mul_left_cancel hpos heq

private theorem prod_range_notdvd_t_eq (p J : ℕ) :
    ∏ t ∈ (Finset.range (p * J)).filter (fun t => ¬ p ∣ t), t
      = ∏ t ∈ (Finset.range (p * J)).filter
        (fun t => ¬ p ∣ t + 1), (t + 1) := by
  have hset := filter_range_eq_filter_Icc p (p * J) J rfl
  have h1 : (∏ t ∈ (Finset.range (p * J)).filter
        (fun t => ¬ p ∣ t), t)
      = ∏ i ∈ (Finset.Icc 1 (p * J)).filter (fun i => ¬ p ∣ i), i := by
    rw [hset]
  have h2 : (∏ t ∈ (Finset.range (p * J)).filter
        (fun t => ¬ p ∣ t + 1), (t + 1))
      = ∏ i ∈ (Finset.Icc 1 (p * J)).filter (fun i => ¬ p ∣ i), i :=
    prod_range_notdvd_eq p (p * J)
  rw [h1, ← h2]

private theorem card_filter_dvd_range (p J : ℕ) (hp : 0 < p) :
    ((Finset.range (p * J)).filter (fun t => p ∣ t)).card = J := by
  have himg := image_range_mul_eq_filter p J hp
  have hinj : Function.Injective (fun s => p * s) := by
    intro a b h
    exact Nat.mul_left_cancel hp h
  have hcard_img : (Finset.image (fun s => p * s)
      (Finset.range J)).card = (Finset.range J).card :=
    Finset.card_image_of_injective _ hinj
  rw [himg] at hcard_img
  rw [hcard_img, Finset.card_range]

private theorem card_filter_notdvd_range (p J : ℕ) (hp : 0 < p) :
    ((Finset.range (p * J)).filter (fun t => ¬ p ∣ t)).card
      = p * J - J := by
  have hcard_range : (Finset.range (p * J)).card = p * J :=
    Finset.card_range _
  have hcard_p := card_filter_dvd_range p J hp
  have hadd : ((Finset.range (p * J)).filter (fun t => p ∣ t)).card +
      ((Finset.range (p * J)).filter (fun t => ¬ p ∣ t)).card
      = (Finset.range (p * J)).card :=
    Finset.card_filter_add_card_filter_not _
  omega

private theorem card_filter_even_of_odd (p J : ℕ) [Fact (Nat.Prime p)]
    (hp2 : p ≠ 2) : Even
    ((Finset.range (p * J)).filter (fun t => ¬ p ∣ t)).card := by
  have hp : Nat.Prime p := Fact.out
  have hp0 : 0 < p := hp.pos
  have hcard := card_filter_notdvd_range p J hp0
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hodd
  have hpeq : p = 2 * k + 1 := hk
  have hcard_eq : ((Finset.range (p * J)).filter
      (fun t => ¬ p ∣ t)).card = 2 * (k * J) := by
    rw [hcard]
    have e1 : p * J = (2 * k + 1) * J := by rw [← hpeq]
    have e2 : (2 * k + 1) * J = 2 * (k * J) + J := by ring
    rw [e1, e2]
    omega
  rw [hcard_eq]
  exact even_two_mul _

private theorem card_filter_even_of_even_J (p J : ℕ) (hp : 0 < p)
    (hJ : Even J) : Even
    ((Finset.range (p * J)).filter (fun t => ¬ p ∣ t)).card := by
  have hcard := card_filter_notdvd_range p J hp
  obtain ⟨r, hr⟩ := hJ
  have h1p : 1 ≤ p := hp
  have hJle : J ≤ p * J := by
    calc J = J * 1 := by rw [mul_one]
      _ ≤ J * p := Nat.mul_le_mul_left J h1p
      _ = p * J := by rw [mul_comm]
  have hcard_eq : ((Finset.range (p * J)).filter
      (fun t => ¬ p ∣ t)).card = (p - 1) * J := by
    rw [hcard]
    have e : p * J - J = (p - 1) * J := by
      have h : (p - 1) * J + J = p * J := by
        have hsub : p - 1 + 1 = p := Nat.sub_add_cancel h1p
        calc (p - 1) * J + J = (p - 1) * J + 1 * J := by rw [one_mul]
          _ = ((p - 1) + 1) * J := by rw [Nat.add_mul]
          _ = p * J := by rw [hsub]
      omega
    exact e
  rw [hcard_eq, hr]
  exact ⟨(p - 1) * r, Nat.mul_add _ _ _⟩

private theorem coprime_prod_range_filter (p K k : ℕ) [Fact (Nat.Prime p)] :
    Nat.Coprime
      (∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t + 1), (t + 1))
      (p ^ k) := by
  have hp : Nat.Prime p := Fact.out
  rw [Nat.coprime_prod_left_iff]
  intro t ht
  have hndvd : ¬ p ∣ t + 1 := (Finset.mem_filter.mp ht).2
  have h1 : Nat.Coprime p (t + 1) := (hp.coprime_iff_not_dvd).mpr hndvd
  have h2 : Nat.Coprime (t + 1) p := h1.symm
  exact h2.pow_right k

private theorem prod_unit_sign (p N K J k : ℕ) (hK : K = p * J)
    (hNdiv : p ^ k ∣ N) (hKN : K ≤ N) :
    (((∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t), (N - t) : ℕ))
      : ZMod (p ^ k))
      = (-1) ^ ((Finset.range K).filter (fun t => ¬ p ∣ t)).card *
        (((∏ t ∈ (Finset.range K).filter
          (fun t => ¬ p ∣ t + 1), (t + 1) : ℕ)) : ZMod (p ^ k)) := by
  have hN0 : ((N : ℕ) : ZMod (p ^ k)) = 0 :=
    (ZMod.natCast_eq_zero_iff N (p ^ k)).mpr hNdiv
  have hterm : ∀ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t),
      (((N - t : ℕ)) : ZMod (p ^ k)) = -((t : ℕ) : ZMod (p ^ k)) := by
    intro t ht
    have hmem := Finset.mem_filter.mp ht
    have htK : t < K := Finset.mem_range.mp hmem.1
    have htN : t ≤ N := by omega
    rw [Nat.cast_sub htN, hN0, zero_sub]
  have hprod : (∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t),
        (((N - t : ℕ)) : ZMod (p ^ k)))
      = ∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t),
        (-((t : ℕ) : ZMod (p ^ k))) :=
    Finset.prod_congr rfl hterm
  have hneg : (∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t),
        (-((t : ℕ) : ZMod (p ^ k))))
      = (-1) ^ ((Finset.range K).filter (fun t => ¬ p ∣ t)).card *
        (∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t),
          ((t : ℕ) : ZMod (p ^ k))) := by
    have e : ∀ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t),
        (-((t : ℕ) : ZMod (p ^ k))) = (-1) * ((t : ℕ) : ZMod (p ^ k)) := by
      intro t _
      rw [neg_one_mul]
    rw [Finset.prod_congr rfl e]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hcastT : (∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t),
        ((t : ℕ) : ZMod (p ^ k)))
      = (((∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t), t : ℕ))
        : ZMod (p ^ k)) := by
    simp only [Nat.cast_prod]
  have hTeq : (∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t), t)
      = ∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t + 1), (t + 1) := by
    rw [hK]
    exact prod_range_notdvd_t_eq p J
  simp only [Nat.cast_prod] at hprod ⊢
  rw [hprod, hneg, hcastT, hTeq, Nat.cast_prod]

private theorem choose_mul_prod_range_aux (N K : ℕ) :
    Nat.choose N K * (∏ t ∈ Finset.range K, (t + 1))
      = ∏ t ∈ Finset.range K, (N - t) := by
  by_cases hKN : K ≤ N
  · have h1 := Nat.choose_mul_factorial_mul_factorial hKN
    have h2 := prod_range_sub_mul_factorial N K hKN
    have h3 := prod_range_add_one_eq_factorial K
    have hpos : 0 < Nat.factorial (N - K) := Nat.factorial_pos _
    have hmul : (Nat.choose N K * (∏ t ∈ Finset.range K, (t + 1)))
        * Nat.factorial (N - K)
        = (∏ t ∈ Finset.range K, (N - t)) * Nat.factorial (N - K) := by
      rw [mul_assoc, h3]
      have hcomm : Nat.factorial K * Nat.factorial (N - K)
          = Nat.factorial (N - K) * Nat.factorial K := by
        rw [mul_comm]
      rw [hcomm, ← mul_assoc]
      have h1' : Nat.choose N K * Nat.factorial (N - K)
          * Nat.factorial K = Nat.factorial N := by
        rw [mul_assoc] at h1 ⊢
        rw [mul_comm (Nat.factorial K) (Nat.factorial (N - K))] at h1
        exact h1
      rw [h1']
      exact h2.symm
    exact Nat.mul_right_cancel hpos hmul
  · have hlt : N < K := by omega
    have hC0 : Nat.choose N K = 0 := Nat.choose_eq_zero_of_lt hlt
    have hP0 : (∏ t ∈ Finset.range K, (N - t)) = 0 := by
      have hmem : N ∈ Finset.range K := Finset.mem_range.mpr hlt
      have hterm : N - N = 0 := Nat.sub_self N
      exact Finset.prod_eq_zero hmem hterm
    rw [hC0, hP0, Nat.zero_mul]

private theorem choose_range_unit_eq (p N M K J : ℕ) (hp : 0 < p)
    (hN : N = p * M) (hK : K = p * J) :
    Nat.choose N K *
        (∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t + 1), (t + 1))
      = Nat.choose M J *
        (∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t), (N - t)) := by
  have hCD1 := choose_mul_prod_range_aux N K
  have hCD2 := choose_mul_prod_range_aux M J
  have hsplitP := Finset.prod_filter_mul_prod_filter_not
    (Finset.range K) (fun t => p ∣ t) (fun t => N - t)
  have hsplitD := Finset.prod_filter_mul_prod_filter_not
    (Finset.range K) (fun t => p ∣ t + 1) (fun t => t + 1)
  have hDp : ∏ t ∈ (Finset.range K).filter (fun t => p ∣ t + 1), (t + 1)
      = p ^ J * ∏ s ∈ Finset.range J, (s + 1) := by
    rw [hK]
    exact prod_range_dvd_succ_eq p J hp
  have hPp : ∏ t ∈ (Finset.range K).filter (fun t => p ∣ t), (N - t)
      = p ^ J * ∏ s ∈ Finset.range J, (M - s) := by
    rw [hK, hN]
    exact prod_range_filter_sub_eq p J M hp
  have hposP : 0 < p ^ J := Nat.pow_pos hp
  have hposE : 0 < ∏ s ∈ Finset.range J, (s + 1) := by
    apply Finset.prod_pos
    intro s hs
    omega
  have hposPE : 0 < p ^ J * ∏ s ∈ Finset.range J, (s + 1) :=
    Nat.mul_pos hposP hposE
  have heq : (p ^ J * ∏ s ∈ Finset.range J, (s + 1)) *
        (Nat.choose N K *
          ∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t + 1), (t + 1))
      = (p ^ J * ∏ s ∈ Finset.range J, (s + 1)) *
        (Nat.choose M J *
          ∏ t ∈ (Finset.range K).filter (fun t => ¬ p ∣ t), (N - t)) := by
    have e1 : Nat.choose N K * (∏ t ∈ Finset.range K, (t + 1))
        = ∏ t ∈ Finset.range K, (N - t) := hCD1
    rw [← hsplitD, ← hsplitP] at e1
    rw [hDp, hPp] at e1
    have e2 : ∏ s ∈ Finset.range J, (M - s)
        = Nat.choose M J * ∏ s ∈ Finset.range J, (s + 1) := by
      exact hCD2.symm
    rw [e2] at e1
    ring_nf at e1 ⊢
    exact e1
  exact Nat.mul_left_cancel hposPE heq

private theorem choose_mul_prod_range (N K : ℕ) :
    Nat.choose N K * (∏ t ∈ Finset.range K, (t + 1))
      = ∏ t ∈ Finset.range K, (N - t) := by
  by_cases hKN : K ≤ N
  · have h1 := Nat.choose_mul_factorial_mul_factorial hKN
    have h2 := prod_range_sub_mul_factorial N K hKN
    have h3 := prod_range_add_one_eq_factorial K
    have hpos : 0 < Nat.factorial (N - K) := Nat.factorial_pos _
    have hmul : (Nat.choose N K * (∏ t ∈ Finset.range K, (t + 1)))
        * Nat.factorial (N - K)
        = (∏ t ∈ Finset.range K, (N - t)) * Nat.factorial (N - K) := by
      rw [mul_assoc, h3]
      have hcomm : Nat.factorial K * Nat.factorial (N - K)
          = Nat.factorial (N - K) * Nat.factorial K := by
        rw [mul_comm]
      rw [hcomm, ← mul_assoc]
      have h1' : Nat.choose N K * Nat.factorial (N - K)
          * Nat.factorial K = Nat.factorial N := by
        rw [mul_assoc] at h1 ⊢
        rw [mul_comm (Nat.factorial K) (Nat.factorial (N - K))] at h1
        exact h1
      rw [h1']
      exact h2.symm
    exact Nat.mul_right_cancel hpos hmul
  · have hlt : N < K := by omega
    have hC0 : Nat.choose N K = 0 := Nat.choose_eq_zero_of_lt hlt
    have hP0 : (∏ t ∈ Finset.range K, (N - t)) = 0 := by
      have hmem : N ∈ Finset.range K := Finset.mem_range.mpr hlt
      have hterm : N - N = 0 := Nat.sub_self N
      exact Finset.prod_eq_zero hmem hterm
    rw [hC0, hP0, Nat.zero_mul]

private theorem choose_add_prime_pow_congr (p t n j : ℕ)
    [Fact (Nat.Prime p)] :
    Nat.choose (p ^ (t + 1) * n + p * j) (p * j)
      ≡ Nat.choose (p ^ t * n + j) j [MOD p ^ (t + 1)] := by
  have hp : Nat.Prime p := Fact.out
  have hp0 : 0 < p := hp.pos
  have hN : p ^ (t + 1) * n = p * (p ^ t * n) := by
    rw [pow_succ', mul_assoc]
  have hNdiv : p ^ (t + 1) ∣ p ^ (t + 1) * n := dvd_mul_right _ _
  have hunit := choose_add_unit_eq p (p ^ (t + 1) * n) (p ^ t * n)
    (p * j) j hp0 hN rfl
  have hPuDu := prod_unit_congr_add p (p ^ (t + 1) * n) (p * j)
    (t + 1) hNdiv
  have hcop := coprime_prod_filter p (p * j) (t + 1)
  have hcast : (((Nat.choose (p ^ (t + 1) * n + p * j) (p * j) : ℕ))
      : ZMod (p ^ (t + 1)))
      * (((∏ i ∈ (Finset.Icc 1 (p * j)).filter
        (fun i => ¬ p ∣ i), i : ℕ)) : ZMod (p ^ (t + 1)))
      = (((Nat.choose (p ^ t * n + j) j : ℕ)) : ZMod (p ^ (t + 1)))
      * (((∏ i ∈ (Finset.Icc 1 (p * j)).filter
        (fun i => ¬ p ∣ i), (p ^ (t + 1) * n + i) : ℕ))
        : ZMod (p ^ (t + 1))) := by
    have h := congrArg (fun x : ℕ => ((x : ℕ) : ZMod (p ^ (t + 1)))) hunit
    simp only [Nat.cast_mul] at h
    exact h
  rw [hPuDu] at hcast
  have hunit_isunit : IsUnit
      ((((∏ i ∈ (Finset.Icc 1 (p * j)).filter
        (fun i => ¬ p ∣ i), i : ℕ))) : ZMod (p ^ (t + 1))) := by
    have hu := (ZMod.unitOfCoprime _ hcop).isUnit
    rwa [ZMod.coe_unitOfCoprime] at hu
  have hZMod : (((Nat.choose (p ^ (t + 1) * n + p * j) (p * j) : ℕ))
      : ZMod (p ^ (t + 1)))
      = ((Nat.choose (p ^ t * n + j) j : ℕ) : ZMod (p ^ (t + 1))) :=
    IsUnit.mul_right_cancel hunit_isunit hcast
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hZMod

private theorem dvd_choose_of_not_dvd_aux (p N K m : ℕ)
    [Fact (Nat.Prime p)] (hKN : K ≤ N) (hK0 : 0 < K)
    (hNdvd : p ^ m ∣ N) (hKndvd : ¬ p ∣ K) :
    p ^ m ∣ Nat.choose N K := by
  have hp : Nat.Prime p := Fact.out
  obtain ⟨N', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
    (by omega : N ≠ 0)
  obtain ⟨K', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
    (by omega : K ≠ 0)
  have heq : (K' + 1) * Nat.choose (N' + 1) (K' + 1)
      = (N' + 1) * Nat.choose N' K' := by
    have h := Nat.add_one_mul_choose_eq N' K'
    calc (K' + 1) * Nat.choose (N' + 1) (K' + 1)
        = Nat.choose (N' + 1) (K' + 1) * (K' + 1) := by rw [mul_comm]
      _ = (N' + 1) * Nat.choose N' K' := h.symm
  have hdvd : p ^ m ∣ (K' + 1) * Nat.choose (N' + 1) (K' + 1) := by
    rw [heq]
    exact hNdvd.mul_right _
  have hcop : Nat.Coprime (p ^ m) (K' + 1) := by
    have h1 : Nat.Coprime p (K' + 1) :=
      (hp.coprime_iff_not_dvd).mpr hKndvd
    exact h1.pow_left m
  exact (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd)

private theorem choose_prime_pow_congr_aux (p t n j : ℕ)
    [Fact (Nat.Prime p)] (hJle : j ≤ p ^ t * n) :
    Nat.choose (p ^ (t + 1) * n) (p * j)
      ≡ Nat.choose (p ^ t * n) j [MOD p ^ (t + 1)] := by
  have hp : Nat.Prime p := Fact.out
  have hp0 : 0 < p := hp.pos
  have hN : p ^ (t + 1) * n = p * (p ^ t * n) := by
    rw [pow_succ', mul_assoc]
  have hNdiv : p ^ (t + 1) ∣ p ^ (t + 1) * n := dvd_mul_right _ _
  have hKN : p * j ≤ p ^ (t + 1) * n := by
    rw [hN]
    exact Nat.mul_le_mul_left p hJle
  have hunit := choose_range_unit_eq p (p ^ (t + 1) * n) (p ^ t * n)
    (p * j) j hp0 hN rfl
  have hsign := prod_unit_sign p (p ^ (t + 1) * n) (p * j) j (t + 1)
    rfl hNdiv hKN
  have hcop := coprime_prod_range_filter p (p * j) (t + 1)
  have hcast : (((Nat.choose (p ^ (t + 1) * n) (p * j) : ℕ))
      : ZMod (p ^ (t + 1)))
      * (((∏ u ∈ (Finset.range (p * j)).filter
        (fun u => ¬ p ∣ u + 1), (u + 1) : ℕ)) : ZMod (p ^ (t + 1)))
      = (((Nat.choose (p ^ t * n) j : ℕ)) : ZMod (p ^ (t + 1)))
      * (((∏ u ∈ (Finset.range (p * j)).filter
        (fun u => ¬ p ∣ u), (p ^ (t + 1) * n - u) : ℕ))
        : ZMod (p ^ (t + 1))) := by
    have h := congrArg (fun x : ℕ => ((x : ℕ) : ZMod (p ^ (t + 1)))) hunit
    simp only [Nat.cast_mul] at h
    exact h
  rw [hsign] at hcast
  have hunit_isunit : IsUnit
      ((((∏ u ∈ (Finset.range (p * j)).filter
        (fun u => ¬ p ∣ u + 1), (u + 1) : ℕ)))
        : ZMod (p ^ (t + 1))) := by
    have hu := (ZMod.unitOfCoprime _ hcop).isUnit
    rwa [ZMod.coe_unitOfCoprime] at hu
  have hcard := card_filter_notdvd_range p j hp0
  by_cases hp2 : p = 2
  · subst hp2
    by_cases hJeven : Even j
    · have heven : Even
          ((Finset.range (2 * j)).filter (fun t => ¬ 2 ∣ t)).card :=
        card_filter_even_of_even_J 2 j (by omega) hJeven
      have hpow1 : ((-1 : ZMod (2 ^ (t + 1)))
          ^ ((Finset.range (2 * j)).filter
            (fun t => ¬ 2 ∣ t)).card) = 1 :=
        heven.neg_one_pow
      rw [hpow1, one_mul] at hcast
      have hZMod : (((Nat.choose (2 ^ (t + 1) * n) (2 * j) : ℕ))
          : ZMod (2 ^ (t + 1)))
          = ((Nat.choose (2 ^ t * n) j : ℕ) : ZMod (2 ^ (t + 1))) :=
        IsUnit.mul_right_cancel hunit_isunit hcast
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hZMod
    · have hodd : Odd j := by
        rcases Nat.even_or_odd j with h | h
        · exact absurd h hJeven
        · exact h
      have hpowm1 : ((-1 : ZMod (2 ^ (t + 1)))
          ^ ((Finset.range (2 * j)).filter
            (fun t => ¬ 2 ∣ t)).card) = -1 := by
        have hcardJ : ((Finset.range (2 * j)).filter
            (fun t => ¬ 2 ∣ t)).card = j := by
          have h := card_filter_notdvd_range 2 j (by omega)
          omega
        rw [hcardJ]
        exact hodd.neg_one_pow
      rw [hpowm1] at hcast
      have hneg : (((Nat.choose (2 ^ (t + 1) * n) (2 * j) : ℕ))
          : ZMod (2 ^ (t + 1)))
          = -(((Nat.choose (2 ^ t * n) j : ℕ))
            : ZMod (2 ^ (t + 1))) := by
        have h' : (((Nat.choose (2 ^ (t + 1) * n) (2 * j) : ℕ))
            : ZMod (2 ^ (t + 1)))
            * (((∏ u ∈ (Finset.range (2 * j)).filter
              (fun u => ¬ 2 ∣ u + 1), (u + 1) : ℕ))
              : ZMod (2 ^ (t + 1)))
            = (-(((Nat.choose (2 ^ t * n) j : ℕ))
              : ZMod (2 ^ (t + 1))))
            * (((∏ u ∈ (Finset.range (2 * j)).filter
              (fun u => ¬ 2 ∣ u + 1), (u + 1) : ℕ))
              : ZMod (2 ^ (t + 1))) := by
          have hDu_eq : (((∏ t ∈ (Finset.range (2 * j)).filter
              (fun t => ¬ 2 ∣ t + 1), (t + 1) : ℕ))
              : ZMod (2 ^ (t + 1)))
              = (((∏ u ∈ (Finset.range (2 * j)).filter
                (fun u => ¬ 2 ∣ u + 1), (u + 1) : ℕ))
                : ZMod (2 ^ (t + 1))) :=
            rfl
          rw [hDu_eq] at hcast
          have heq : (((Nat.choose (2 ^ t * n) j : ℕ))
              : ZMod (2 ^ (t + 1)))
              * ((-1) * (((∏ u ∈ (Finset.range (2 * j)).filter
                (fun u => ¬ 2 ∣ u + 1), (u + 1) : ℕ))
                : ZMod (2 ^ (t + 1))))
              = (-(((Nat.choose (2 ^ t * n) j : ℕ))
                : ZMod (2 ^ (t + 1))))
              * (((∏ u ∈ (Finset.range (2 * j)).filter
                (fun u => ¬ 2 ∣ u + 1), (u + 1) : ℕ))
                : ZMod (2 ^ (t + 1))) := by
            ring
          rw [heq] at hcast
          exact hcast
        exact IsUnit.mul_right_cancel hunit_isunit h'
      have h2dvd : 2 ^ t ∣ Nat.choose (2 ^ t * n) j := by
        have hJpos : 0 < j := by
          obtain ⟨k, hk⟩ := hodd
          omega
        have hMdiv : 2 ^ t ∣ 2 ^ t * n := dvd_mul_right _ _
        have hndvd : ¬ 2 ∣ j := by
          intro hdvd
          have hev : Even j := even_iff_two_dvd.mpr hdvd
          exact hJeven hev
        exact dvd_choose_of_not_dvd_aux 2 (2 ^ t * n) j t hJle hJpos hMdiv hndvd
      obtain ⟨c, hc⟩ := h2dvd
      have h2mul0 : (2 : ZMod (2 ^ (t + 1)))
          * (((Nat.choose (2 ^ t * n) j : ℕ)) : ZMod (2 ^ (t + 1))) = 0 := by
        have hdiv : 2 ^ (t + 1) ∣ 2 * Nat.choose (2 ^ t * n) j := by
          rw [hc, pow_succ']
          exact Dvd.intro c (by ring)
        have hcast0 : ((((2 * Nat.choose (2 ^ t * n) j : ℕ)))
            : ZMod (2 ^ (t + 1))) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
        simp only [Nat.cast_mul, Nat.cast_ofNat] at hcast0
        exact hcast0
      have hselfneg : (-(((Nat.choose (2 ^ t * n) j : ℕ))
          : ZMod (2 ^ (t + 1))))
          = (((Nat.choose (2 ^ t * n) j : ℕ)) : ZMod (2 ^ (t + 1))) := by
        have h2' : (((Nat.choose (2 ^ t * n) j : ℕ))
            : ZMod (2 ^ (t + 1)))
            + (((Nat.choose (2 ^ t * n) j : ℕ)) : ZMod (2 ^ (t + 1))) = 0 := by
          have h := h2mul0
          rwa [two_mul] at h
        have h0 : (((Nat.choose (2 ^ t * n) j : ℕ)) : ZMod (2 ^ (t + 1)))
            + (-(((Nat.choose (2 ^ t * n) j : ℕ))
              : ZMod (2 ^ (t + 1)))) = 0 :=
          add_neg_cancel _
        have heq : (((Nat.choose (2 ^ t * n) j : ℕ)) : ZMod (2 ^ (t + 1)))
            + (((Nat.choose (2 ^ t * n) j : ℕ)) : ZMod (2 ^ (t + 1)))
            = (((Nat.choose (2 ^ t * n) j : ℕ)) : ZMod (2 ^ (t + 1)))
            + (-(((Nat.choose (2 ^ t * n) j : ℕ))
              : ZMod (2 ^ (t + 1)))) := by
          rw [h2', h0]
        have hcancel := add_left_cancel heq
        exact hcancel.symm
      have hZMod : (((Nat.choose (2 ^ (t + 1) * n) (2 * j) : ℕ))
          : ZMod (2 ^ (t + 1)))
          = ((Nat.choose (2 ^ t * n) j : ℕ) : ZMod (2 ^ (t + 1))) := by
        rw [hneg, hselfneg]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hZMod
  · have heven : Even
        ((Finset.range (p * j)).filter (fun t => ¬ p ∣ t)).card :=
      card_filter_even_of_odd p j hp2
    have hpow1 : ((-1 : ZMod (p ^ (t + 1)))
        ^ ((Finset.range (p * j)).filter
          (fun t => ¬ p ∣ t)).card) = 1 :=
      heven.neg_one_pow
    rw [hpow1, one_mul] at hcast
    have hZMod : (((Nat.choose (p ^ (t + 1) * n) (p * j) : ℕ))
        : ZMod (p ^ (t + 1)))
        = ((Nat.choose (p ^ t * n) j : ℕ) : ZMod (p ^ (t + 1))) :=
      IsUnit.mul_right_cancel hunit_isunit hcast
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hZMod

private theorem choose_prime_pow_congr (p t n j : ℕ)
    [Fact (Nat.Prime p)] :
    Nat.choose (p ^ (t + 1) * n) (p * j)
      ≡ Nat.choose (p ^ t * n) j [MOD p ^ (t + 1)] := by
  by_cases hJle : j ≤ p ^ t * n
  · exact choose_prime_pow_congr_aux p t n j hJle
  · have hp : Nat.Prime p := Fact.out
    have hp0 : 0 < p := hp.pos
    have hltM : p ^ t * n < j := by omega
    have hN : p ^ (t + 1) * n = p * (p ^ t * n) := by
      rw [pow_succ', mul_assoc]
    have hltN : p ^ (t + 1) * n < p * j := by
      rw [hN]
      exact (Nat.mul_lt_mul_left hp0).mpr hltM
    have hC1 : Nat.choose (p ^ (t + 1) * n) (p * j) = 0 :=
      Nat.choose_eq_zero_of_lt hltN
    have hC2 : Nat.choose (p ^ t * n) j = 0 :=
      Nat.choose_eq_zero_of_lt hltM
    rw [hC1, hC2]

private theorem dvd_choose_of_not_dvd (p N K m : ℕ) [Fact (Nat.Prime p)]
    (hKN : K ≤ N) (hK0 : 0 < K) (hNdvd : p ^ m ∣ N) (hKndvd : ¬ p ∣ K) :
    p ^ m ∣ Nat.choose N K := by
  have hp : Nat.Prime p := Fact.out
  obtain ⟨N', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
    (by omega : N ≠ 0)
  obtain ⟨K', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
    (by omega : K ≠ 0)
  have heq : (K' + 1) * Nat.choose (N' + 1) (K' + 1)
      = (N' + 1) * Nat.choose N' K' := by
    have h := Nat.add_one_mul_choose_eq N' K'
    calc (K' + 1) * Nat.choose (N' + 1) (K' + 1)
        = Nat.choose (N' + 1) (K' + 1) * (K' + 1) := by rw [mul_comm]
      _ = (N' + 1) * Nat.choose N' K' := h.symm
  have hdvd : p ^ m ∣ (K' + 1) * Nat.choose (N' + 1) (K' + 1) := by
    rw [heq]
    exact hNdvd.mul_right _
  have hcop : Nat.Coprime (p ^ m) (K' + 1) := by
    have h1 : Nat.Coprime p (K' + 1) :=
      (hp.coprime_iff_not_dvd).mpr hKndvd
    exact h1.pow_left m
  exact (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd)

private theorem binomialPowerSeq_moebius_nonneg (r s n : ℕ) (hr : 0 < r)
    (hn : 0 < n) :
    0 ≤ ∑ d ∈ Nat.divisors n,
      (⇑ArithmeticFunction.moebius d) *
        ((binomialPowerSeq r s (n / d) : ℕ) : ℤ) := by
  have h1mem : 1 ∈ Nat.divisors n :=
    Nat.one_mem_divisors.mpr (by omega)
  have hdecomp := Finset.add_sum_erase (Nat.divisors n)
    (fun d => (⇑ArithmeticFunction.moebius d) *
      ((binomialPowerSeq r s (n / d) : ℕ) : ℤ)) h1mem
  have hmu1 : (⇑ArithmeticFunction.moebius 1) = 1 :=
    ArithmeticFunction.moebius_apply_one
  have hn1 : n / 1 = n := Nat.div_one n
  have hterm1 : (⇑ArithmeticFunction.moebius 1) *
      ((binomialPowerSeq r s (n / 1) : ℕ) : ℤ) =
      ((binomialPowerSeq r s n : ℕ) : ℤ) := by
    rw [hmu1, hn1, one_mul]
  rw [hterm1] at hdecomp
  have hlower : ∀ d ∈ (Nat.divisors n).erase 1,
      -((binomialPowerSeq r s (n / d) : ℕ) : ℤ) ≤
        (⇑ArithmeticFunction.moebius d) *
          ((binomialPowerSeq r s (n / d) : ℕ) : ℤ) := by
    intro d _
    have hmu := moebius_ge_neg_one d
    have hnn : 0 ≤ ((binomialPowerSeq r s (n / d) : ℕ) : ℤ) :=
      Int.natCast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hmu hnn
    simp only [neg_one_mul] at hmul
    exact hmul
  have hsumle : (∑ d ∈ (Nat.divisors n).erase 1,
        (-((binomialPowerSeq r s (n / d) : ℕ) : ℤ))) ≤
      ∑ d ∈ (Nat.divisors n).erase 1,
        ((⇑ArithmeticFunction.moebius d) *
          ((binomialPowerSeq r s (n / d) : ℕ) : ℤ)) :=
    Finset.sum_le_sum hlower
  rw [Finset.sum_neg_distrib] at hsumle
  have hcast : (∑ d ∈ (Nat.divisors n).erase 1,
        ((binomialPowerSeq r s (n / d) : ℕ) : ℤ)) =
      (((∑ d ∈ (Nat.divisors n).erase 1,
        binomialPowerSeq r s (n / d)) : ℕ) : ℤ) := by
    simp only [Nat.cast_sum]
  have hnat := binomialPowerSeq_erase_sum_le r s n hr hn
  have hnatZ : (((∑ d ∈ (Nat.divisors n).erase 1,
        binomialPowerSeq r s (n / d)) : ℕ) : ℤ) + 1 ≤
      ((binomialPowerSeq r s n : ℕ) : ℤ) := by
    exact_mod_cast hnat
  omega

private theorem prime_dvd_choose_mul_of_not_dvd (p n k : ℕ) [Fact (Nat.Prime p)]
    (_hle : k ≤ p * n) (hk : ¬ p ∣ k) : p ∣ (p * n).choose k := by
  have hp : Nat.Prime p := Fact.out
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨a, ha⟩ := pow_unbounded_of_one_lt (p * n + k + 1) hp1
  have hpn : p * n < p ^ a := by omega
  have hk2 : k < p ^ a := by omega
  have hluc := Choose.lucas_theorem_nat (n := p * n) (k := k) (p := p) hpn hk2
  have hpm : p * n % p = 0 := Nat.mul_mod_right p n
  have hkr : k % p ≠ 0 := fun h => hk (Nat.dvd_of_mod_eq_zero h)
  have hpos : 0 < k % p := Nat.pos_of_ne_zero hkr
  have e1 : p * n / p ^ 0 % p = 0 := by
    simp only [pow_zero, Nat.div_one]
    exact hpm
  have e2 : k / p ^ 0 % p = k % p := by simp
  have hfactor : (p * n / p ^ 0 % p).choose (k / p ^ 0 % p) = 0 := by
    rw [e1, e2]
    exact Nat.choose_eq_zero_of_lt hpos
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [pow_zero] at ha; omega
    · exact h
  have hprod : ∏ i ∈ Finset.range a, (p * n / p ^ i % p).choose (k / p ^ i % p) = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_range.mpr ha0) hfactor
  have h0 : (p * n).choose k ≡ 0 [MOD p] := hluc.trans (by rw [hprod])
  exact (Nat.modEq_zero_iff_dvd).mp h0

private theorem prime_choose_mul_congr (p N Q : ℕ) [Fact (Nat.Prime p)] :
    (p * N).choose (p * Q) ≡ N.choose Q [MOD p] := by
  have hp : Nat.Prime p := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hp0 : 0 < p := hp.pos
  obtain ⟨b, hb⟩ := pow_unbounded_of_one_lt (p * N + p * Q + 1) hp1
  have hPN : p * N < p ^ b := by omega
  have hPQ : p * Q < p ^ b := by omega
  have hN : N < p ^ b :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left N hp0) hPN
  have hQ : Q < p ^ b :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left Q hp0) hPQ
  have hle : p ^ b ≤ p ^ (b + 1) :=
    Nat.pow_le_pow_right hp0 (Nat.le_succ b)
  have hPN' : p * N < p ^ (b + 1) := lt_of_lt_of_le hPN hle
  have hPQ' : p * Q < p ^ (b + 1) := lt_of_lt_of_le hPQ hle
  have hN' : N < p ^ (b + 1) := lt_of_lt_of_le hN hle
  have hQ' : Q < p ^ (b + 1) := lt_of_lt_of_le hQ hle
  have hluc1 := Choose.lucas_theorem_nat (n := p * N) (k := p * Q) (p := p) hPN' hPQ'
  have hluc2 := Choose.lucas_theorem_nat (n := N) (k := Q) (p := p) hN' hQ'
  have hshift : ∀ j : ℕ, (p * N) / p ^ (j + 1) % p = N / p ^ j % p := by
    intro j
    have e : p ^ (j + 1) = p * p ^ j := pow_succ' p j
    rw [e, Nat.mul_div_mul_left _ _ hp0]
  have hshift2 : ∀ j : ℕ, (p * Q) / p ^ (j + 1) % p = Q / p ^ j % p := by
    intro j
    have e : p ^ (j + 1) = p * p ^ j := pow_succ' p j
    rw [e, Nat.mul_div_mul_left _ _ hp0]
  have htop2 : N / p ^ b % p = 0 := by
    have h : N / p ^ b = 0 := Nat.div_eq_of_lt hN
    rw [h, Nat.zero_mod]
  have htop2' : Q / p ^ b % p = 0 := by
    have h : Q / p ^ b = 0 := Nat.div_eq_of_lt hQ
    rw [h, Nat.zero_mod]
  have hbot : (p * N) / p ^ 0 % p = 0 := by
    simp only [pow_zero, Nat.div_one]
    exact Nat.mul_mod_right p N
  have hbot' : (p * Q) / p ^ 0 % p = 0 := by
    simp only [pow_zero, Nat.div_one]
    exact Nat.mul_mod_right p Q
  have hF0 : ((p * N) / p ^ 0 % p).choose ((p * Q) / p ^ 0 % p) = 1 := by
    simp only [hbot, hbot', Nat.choose_zero_right]
  have hGb : (N / p ^ b % p).choose (Q / p ^ b % p) = 1 := by
    simp only [htop2, htop2', Nat.choose_zero_right]
  have hmid : (∏ k ∈ Finset.range b, ((p * N) / p ^ (k + 1) % p).choose ((p * Q) / p ^ (k + 1) % p))
      = ∏ k ∈ Finset.range b, (N / p ^ k % p).choose (Q / p ^ k % p) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hshift j, hshift2 j]
  have hprod_eq : (∏ i ∈ Finset.range (b + 1), ((p * N) / p ^ i % p).choose ((p * Q) / p ^ i % p))
      = ∏ j ∈ Finset.range (b + 1), (N / p ^ j % p).choose (Q / p ^ j % p) := by
    rw [Finset.prod_range_succ' (fun i => ((p * N) / p ^ i % p).choose ((p * Q) / p ^ i % p)) b]
    rw [Finset.prod_range_succ (fun j => (N / p ^ j % p).choose (Q / p ^ j % p)) b]
    rw [hmid, hF0, hGb, mul_one]
  exact hluc1.trans (by rw [hprod_eq]; exact hluc2.symm)

private theorem binomialPowerSeq_prime_mul_zmod (p r s n : ℕ) [Fact (Nat.Prime p)] (hr : 0 < r) :
    ((binomialPowerSeq r s (p * n) : ℕ) : ZMod p) = ((binomialPowerSeq r s n : ℕ) : ZMod p) := by
  have hp : Nat.Prime p := Fact.out
  have hp0 : 0 < p := hp.pos
  have hrne : r ≠ 0 := ne_of_gt hr
  have hcast : ∀ m : ℕ, ((binomialPowerSeq r s m : ℕ) : ZMod p)
      = ∑ k ∈ Finset.range (m + 1),
        (((Nat.choose m k : ℕ) : ZMod p) ^ r * (((Nat.choose (m + k) k : ℕ)) : ZMod p) ^ s) := by
    intro m
    unfold binomialPowerSeq
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp [Nat.cast_mul, Nat.cast_pow]
  rw [hcast (p * n), hcast n]
  set F : ℕ → ZMod p := fun k =>
    (((Nat.choose (p * n) k : ℕ) : ZMod p) ^ r *
      (((Nat.choose (p * n + k) k : ℕ)) : ZMod p) ^ s) with hF
  set G : ℕ → ZMod p := fun q =>
    (((Nat.choose n q : ℕ) : ZMod p) ^ r * (((Nat.choose (n + q) q : ℕ)) : ZMod p) ^ s) with hG
  have hzero : ∀ k ∈ Finset.range (p * n + 1), ¬ p ∣ k → F k = 0 := by
    intro k hk hkd
    have hle : k ≤ p * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hdvd : p ∣ (p * n).choose k := prime_dvd_choose_mul_of_not_dvd p n k hle hkd
    have hcast0 : (((Nat.choose (p * n) k : ℕ)) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hdvd
    simp [hF, hcast0, zero_pow hrne]
  have hsumfilter : ∑ k ∈ Finset.range (p * n + 1), F k
      = ∑ k ∈ (Finset.range (p * n + 1)).filter (fun k => p ∣ k), F k := by
    apply Eq.symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hnk
    have hkd : ¬ p ∣ k := fun hd => hnk (Finset.mem_filter.mpr ⟨hk, hd⟩)
    exact hzero k hk hkd
  have hbij : ∑ k ∈ (Finset.range (p * n + 1)).filter (fun k => p ∣ k), F k
      = ∑ q ∈ Finset.range (n + 1), G q := by
    apply Finset.sum_bij (fun k _ => k / p)
    · intro k hk
      rw [Finset.mem_filter] at hk
      rw [Finset.mem_range] at hk ⊢
      obtain ⟨q, rfl⟩ := hk.2
      have hqn : q ≤ n := by
        apply Nat.le_of_mul_le_mul_left _ hp0
        exact Nat.lt_succ_iff.mp hk.1
      have e : p * q / p = q := (by rw [mul_comm p q]; exact Nat.mul_div_cancel q hp0)
      rw [e]
      exact Nat.lt_succ_iff.mpr hqn
    · intro k1 h1 k2 h2 h12
      rw [Finset.mem_filter] at h1 h2
      obtain ⟨q1, rfl⟩ := h1.2
      obtain ⟨q2, rfl⟩ := h2.2
      have e1 : p * q1 / p = q1 := (by rw [mul_comm p q1]; exact Nat.mul_div_cancel q1 hp0)
      have e2 : p * q2 / p = q2 := (by rw [mul_comm p q2]; exact Nat.mul_div_cancel q2 hp0)
      rw [e1, e2] at h12
      rw [h12]
    · intro q hq
      rw [Finset.mem_range] at hq
      have hqn : q ≤ n := Nat.lt_succ_iff.mp hq
      refine ⟨p * q, ?_, (by rw [mul_comm p q]; exact Nat.mul_div_cancel q hp0)⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.mul_le_mul_left p hqn)), ?_⟩
      exact ⟨q, rfl⟩
    · intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨q, rfl⟩ := hk.2
      have e : p * q / p = q := (by rw [mul_comm p q]; exact Nat.mul_div_cancel q hp0)
      rw [e]
      have e1 : (((Nat.choose (p * n) (p * q) : ℕ)) : ZMod p)
          = (((Nat.choose n q : ℕ)) : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr (prime_choose_mul_congr p n q)
      have eeq : p * n + p * q = p * (n + q) := by ring
      have h2 : (p * (n + q)).choose (p * q) ≡ (n + q).choose q [MOD p] :=
        prime_choose_mul_congr p (n + q) q
      have e2 : (((Nat.choose (p * n + p * q) (p * q) : ℕ)) : ZMod p)
          = (((Nat.choose (n + q) q : ℕ)) : ZMod p) := by
        rw [eeq]
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
      simp only [hF, hG]
      rw [e1, e2]
  rw [hsumfilter]
  exact hbij

private theorem binomialPowerSeq_prime_mul_modEq (p r s n : ℕ) [Fact (Nat.Prime p)] (hr : 0 < r) :
    binomialPowerSeq r s (p * n) ≡ binomialPowerSeq r s n [MOD p] :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mp (binomialPowerSeq_prime_mul_zmod p r s n hr)

private theorem binomialPowerSeq_prime_pow_zmod (p t r s n : ℕ)
    [Fact (Nat.Prime p)] (hr : 0 < r) :
    ((binomialPowerSeq r s (p ^ (t + 1) * n) : ℕ) : ZMod (p ^ (t + 1)))
      = ((binomialPowerSeq r s (p ^ t * n) : ℕ) : ZMod (p ^ (t + 1))) := by
  have hp : Nat.Prime p := Fact.out
  have hp0 : 0 < p := hp.pos
  have hrne : r ≠ 0 := ne_of_gt hr
  have hN : p ^ (t + 1) * n = p * (p ^ t * n) := by
    rw [pow_succ', mul_assoc]
  have hNdiv : p ^ (t + 1) ∣ p ^ (t + 1) * n := dvd_mul_right _ _
  have hcast : ∀ m : ℕ, ((binomialPowerSeq r s m : ℕ) : ZMod (p ^ (t + 1)))
      = ∑ k ∈ Finset.range (m + 1),
        (((Nat.choose m k : ℕ) : ZMod (p ^ (t + 1))) ^ r *
          (((Nat.choose (m + k) k : ℕ)) : ZMod (p ^ (t + 1))) ^ s) := by
    intro m
    unfold binomialPowerSeq
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp [Nat.cast_mul, Nat.cast_pow]
  rw [hcast (p ^ (t + 1) * n), hcast (p ^ t * n)]
  set N := p ^ (t + 1) * n with hNdef
  set M := p ^ t * n with hMdef
  have hNM : N = p * M := hN
  set F : ℕ → ZMod (p ^ (t + 1)) := fun k =>
    (((Nat.choose N k : ℕ) : ZMod (p ^ (t + 1))) ^ r *
      (((Nat.choose (N + k) k : ℕ)) : ZMod (p ^ (t + 1))) ^ s) with hF
  set G : ℕ → ZMod (p ^ (t + 1)) := fun q =>
    (((Nat.choose M q : ℕ) : ZMod (p ^ (t + 1))) ^ r *
      (((Nat.choose (M + q) q : ℕ)) : ZMod (p ^ (t + 1))) ^ s) with hG
  have hzero : ∀ k ∈ Finset.range (N + 1), ¬ p ∣ k → F k = 0 := by
    intro k hk hkd
    have hle : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simp at hkd
      · exact hpos
    have hNdiv' : p ^ (t + 1) ∣ N := by
      rw [hNdef]
      exact hNdiv
    have hdvd : p ^ (t + 1) ∣ Nat.choose N k :=
      dvd_choose_of_not_dvd p N k (t + 1) hle hkpos hNdiv' hkd
    have hpowdvd : p ^ (t + 1) ∣ (Nat.choose N k) ^ r := by
      obtain ⟨u, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hrne
      have e : (Nat.choose N k) ^ (u + 1)
          = Nat.choose N k * (Nat.choose N k) ^ u :=
        pow_succ' _ _
      rw [e]
      exact hdvd.mul_right _
    have hcast0 : (((Nat.choose N k : ℕ)) : ZMod (p ^ (t + 1))) ^ r = 0 := by
      have h0 : (((Nat.choose N k : ℕ)) : ZMod (p ^ (t + 1))) ^ r
          = (((((Nat.choose N k) ^ r : ℕ))) : ZMod (p ^ (t + 1))) := by
        simp only [Nat.cast_pow]
      rw [h0]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hpowdvd
    simp [hF, hcast0]
  have hsumfilter : ∑ k ∈ Finset.range (N + 1), F k
      = ∑ k ∈ (Finset.range (N + 1)).filter (fun k => p ∣ k), F k := by
    apply Eq.symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hnk
    have hkd : ¬ p ∣ k := fun hd => hnk (Finset.mem_filter.mpr ⟨hk, hd⟩)
    exact hzero k hk hkd
  have hbij : ∑ k ∈ (Finset.range (N + 1)).filter (fun k => p ∣ k), F k
      = ∑ q ∈ Finset.range (M + 1), G q := by
    apply Finset.sum_bij (fun k _ => k / p)
    · intro k hk
      rw [Finset.mem_filter] at hk
      rw [Finset.mem_range] at hk ⊢
      obtain ⟨q, rfl⟩ := hk.2
      have hqn : q ≤ M := by
        have hle : p * q ≤ N := Nat.lt_succ_iff.mp hk.1
        rw [hNM] at hle
        exact Nat.le_of_mul_le_mul_left hle hp0
      have e : p * q / p = q := (by rw [mul_comm p q]; exact Nat.mul_div_cancel q hp0)
      rw [e]
      exact Nat.lt_succ_iff.mpr hqn
    · intro k1 h1 k2 h2 h12
      rw [Finset.mem_filter] at h1 h2
      obtain ⟨q1, rfl⟩ := h1.2
      obtain ⟨q2, rfl⟩ := h2.2
      have e1 : p * q1 / p = q1 := (by rw [mul_comm p q1]; exact Nat.mul_div_cancel q1 hp0)
      have e2 : p * q2 / p = q2 := (by rw [mul_comm p q2]; exact Nat.mul_div_cancel q2 hp0)
      rw [e1, e2] at h12
      rw [h12]
    · intro q hq
      rw [Finset.mem_range] at hq
      have hqn : q ≤ M := Nat.lt_succ_iff.mp hq
      refine ⟨p * q, ?_, (by rw [mul_comm p q]; exact Nat.mul_div_cancel q hp0)⟩
      rw [Finset.mem_filter]
      have hleN : p * q ≤ N := by
        rw [hNM]
        exact Nat.mul_le_mul_left p hqn
      refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hleN), ?_⟩
      exact ⟨q, rfl⟩
    · intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨q, rfl⟩ := hk.2
      have e : p * q / p = q := (by rw [mul_comm p q]; exact Nat.mul_div_cancel q hp0)
      rw [e]
      have e1 : (((Nat.choose N (p * q) : ℕ)) : ZMod (p ^ (t + 1)))
          = (((Nat.choose M q : ℕ)) : ZMod (p ^ (t + 1))) := by
        have hmod := choose_prime_pow_congr p t n q
        rw [hNdef, hMdef]
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      have e2 : (((Nat.choose (N + p * q) (p * q) : ℕ))
          : ZMod (p ^ (t + 1)))
          = (((Nat.choose (M + q) q : ℕ)) : ZMod (p ^ (t + 1))) := by
        have hmod := choose_add_prime_pow_congr p t n q
        rw [hNdef, hMdef]
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      simp only [hF, hG]
      rw [e1, e2]
  rw [hsumfilter]
  exact hbij

private theorem binomialPowerSeq_prime_pow_modEq (p t r s n : ℕ)
    [Fact (Nat.Prime p)] (hr : 0 < r) :
    binomialPowerSeq r s (p ^ (t + 1) * n)
      ≡ binomialPowerSeq r s (p ^ t * n) [MOD p ^ (t + 1)] :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mp
    (binomialPowerSeq_prime_pow_zmod p t r s n hr)

private theorem moebius_prime_mul {p e : ℕ} [Fact (Nat.Prime p)]
    (hndvd : ¬ p ∣ e) :
    (⇑ArithmeticFunction.moebius (p * e))
      = -(⇑ArithmeticFunction.moebius e) := by
  have hp : Nat.Prime p := Fact.out
  have hcop : Nat.Coprime p e := (hp.coprime_iff_not_dvd).mpr hndvd
  have hmul := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hprime : (⇑ArithmeticFunction.moebius p) = -1 :=
    ArithmeticFunction.moebius_apply_prime hp
  rw [hmul, hprime, neg_one_mul]

private theorem moebius_eq_zero_of_sq_dvd {p d : ℕ} [Fact (Nat.Prime p)]
    (hdvd : p * p ∣ d) : (⇑ArithmeticFunction.moebius d) = 0 := by
  have hp : Nat.Prime p := Fact.out
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsq
  have hunit := hsq p hdvd
  have h1 : p = 1 := Nat.isUnit_iff.mp hunit
  exact hp.ne_one h1

private theorem dvd_of_dvd_mul_pow_of_not_dvd (p t m0 d : ℕ)
    [Fact (Nat.Prime p)] (hdvd : d ∣ p ^ (t + 1) * m0)
    (hndvd : ¬ p ∣ d) : d ∣ m0 := by
  have hp : Nat.Prime p := Fact.out
  have hcop_p : Nat.Coprime p d := (hp.coprime_iff_not_dvd).mpr hndvd
  have hcop_d : Nat.Coprime d p := hcop_p.symm
  have hcop_pow : Nat.Coprime d (p ^ (t + 1)) := hcop_d.pow_right (t + 1)
  exact hcop_pow.dvd_of_dvd_mul_left hdvd

private theorem mul_dvd_pow_mul_of_dvd (p t m0 e : ℕ) (he : e ∣ m0) :
    p * e ∣ p ^ (t + 1) * m0 := by
  have hppow : p ∣ p ^ (t + 1) := dvd_pow_self p (Nat.succ_ne_zero t)
  exact Nat.mul_dvd_mul hppow he

private theorem div_pow_mul_eq (p t m0 e : ℕ) (he : e ∣ m0) :
    (p ^ (t + 1) * m0) / e = p ^ (t + 1) * (m0 / e) :=
  Nat.mul_div_assoc _ he

private theorem div_pow_mul_prime_eq (p t m0 e : ℕ) (hp0 : 0 < p)
    (he0 : 0 < e) (he : e ∣ m0) :
    (p ^ (t + 1) * m0) / (p * e) = p ^ t * (m0 / e) := by
  obtain ⟨c, hc⟩ := he
  have hdiv : m0 / e = c := by
    rw [hc]
    exact Nat.mul_div_cancel_left c he0
  rw [hdiv]
  have hm0 : m0 = e * c := by
    rw [hc, mul_comm]
  have hpow : p ^ (t + 1) = p * p ^ t := pow_succ' p t
  have hN : p ^ (t + 1) * m0 = (p * e) * (p ^ t * c) := by
    rw [hm0, hpow]
    ring
  rw [hN]
  exact Nat.mul_div_cancel_left _ (Nat.mul_pos hp0 he0)

private theorem filter_divisors_eq (p t m0 : ℕ) [Fact (Nat.Prime p)]
    (hm0 : 0 < m0) :
    (Nat.divisors (p ^ (t + 1) * m0)).filter (fun d => ¬ p ∣ d)
      = (Nat.divisors m0).filter (fun e => ¬ p ∣ e) := by
  have hp : Nat.Prime p := Fact.out
  have hp0 : 0 < p := hp.pos
  have hpowpos : 0 < p ^ (t + 1) := Nat.pow_pos hp0
  have hn0 : p ^ (t + 1) * m0 ≠ 0 := ne_of_gt (Nat.mul_pos hpowpos hm0)
  have hm00 : m0 ≠ 0 := ne_of_gt hm0
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdvd, _⟩, hndvd⟩
    have hdvd0 : d ∣ m0 :=
      dvd_of_dvd_mul_pow_of_not_dvd p t m0 d hdvd hndvd
    exact ⟨⟨hdvd0, hm00⟩, hndvd⟩
  · rintro ⟨⟨hdvd0, _⟩, hndvd⟩
    have hm0dvd : m0 ∣ p ^ (t + 1) * m0 := dvd_mul_left m0 _
    have hdvd : d ∣ p ^ (t + 1) * m0 := dvd_trans hdvd0 hm0dvd
    exact ⟨⟨hdvd, hn0⟩, hndvd⟩

private theorem moebius_sum_reorg (p t m0 : ℕ) [Fact (Nat.Prime p)]
    (hm0 : 0 < m0) (a : ℕ → ℤ) :
    (∑ d ∈ Nat.divisors (p ^ (t + 1) * m0),
      (⇑ArithmeticFunction.moebius d) * a ((p ^ (t + 1) * m0) / d))
      = ∑ e ∈ (Nat.divisors m0).filter (fun e => ¬ p ∣ e),
        (⇑ArithmeticFunction.moebius e) *
          (a (p ^ (t + 1) * (m0 / e)) - a (p ^ t * (m0 / e))) := by
  have hp : Nat.Prime p := Fact.out
  have hp0 : 0 < p := hp.pos
  have hpowpos : 0 < p ^ (t + 1) := Nat.pow_pos hp0
  have hn0 : p ^ (t + 1) * m0 ≠ 0 := ne_of_gt (Nat.mul_pos hpowpos hm0)
  have hm00 : m0 ≠ 0 := ne_of_gt hm0
  have hsplit1 := Finset.sum_filter_add_sum_filter_not
    (Nat.divisors (p ^ (t + 1) * m0)) (fun d => p ∣ d)
    (fun d => (⇑ArithmeticFunction.moebius d) *
      a ((p ^ (t + 1) * m0) / d))
  have hS1 : (∑ d ∈ (Nat.divisors (p ^ (t + 1) * m0)).filter
        (fun d => ¬ p ∣ d),
        (⇑ArithmeticFunction.moebius d) * a ((p ^ (t + 1) * m0) / d))
      = ∑ e ∈ (Nat.divisors m0).filter (fun e => ¬ p ∣ e),
        (⇑ArithmeticFunction.moebius e) * a (p ^ (t + 1) * (m0 / e)) := by
    have hset := filter_divisors_eq p t m0 hm0
    rw [hset]
    apply Finset.sum_congr rfl
    intro e he
    have hdvd0 : e ∣ m0 :=
      Nat.dvd_of_mem_divisors ((Finset.mem_filter.mp he).1)
    have hdiv : (p ^ (t + 1) * m0) / e = p ^ (t + 1) * (m0 / e) :=
      div_pow_mul_eq p t m0 e hdvd0
    rw [hdiv]
  have hS0 : (∑ d ∈ ((Nat.divisors (p ^ (t + 1) * m0)).filter
        (fun d => p ∣ d)).filter (fun d => p * p ∣ d),
        (⇑ArithmeticFunction.moebius d) * a ((p ^ (t + 1) * m0) / d)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hdvd : p * p ∣ d := (Finset.mem_filter.mp hd).2
    have hmu : (⇑ArithmeticFunction.moebius d) = 0 :=
      moebius_eq_zero_of_sq_dvd hdvd
    rw [hmu, zero_mul]
  have hS2 : (∑ d ∈ ((Nat.divisors (p ^ (t + 1) * m0)).filter
        (fun d => p ∣ d)).filter (fun d => ¬ p * p ∣ d),
        (⇑ArithmeticFunction.moebius d) * a ((p ^ (t + 1) * m0) / d))
      = ∑ e ∈ (Nat.divisors m0).filter (fun e => ¬ p ∣ e),
        (⇑ArithmeticFunction.moebius (p * e)) * a (p ^ t * (m0 / e)) := by
    apply Finset.sum_bij (fun d _ => d / p)
    · intro d hd
      simp only [Finset.mem_filter] at hd ⊢
      obtain ⟨⟨hmem, hdvd⟩, hnsq⟩ := hd
      have hdvd_n : d ∣ p ^ (t + 1) * m0 := Nat.dvd_of_mem_divisors hmem
      obtain ⟨c, hc⟩ := hdvd
      have hdc : d / p = c := by
        have hpos : 0 < p := hp0
        have e : d = p * c := hc
        rw [e]
        exact Nat.mul_div_cancel_left c hpos
      have hndvd_c : ¬ p ∣ c := by
        intro hcp
        have hsq : p * p ∣ d := by
          rw [hc]
          exact Nat.mul_dvd_mul_left p hcp
        exact hnsq hsq
      have hc_dvd : c ∣ p ^ (t + 1) * m0 := by
        rw [hc] at hdvd_n
        exact dvd_of_mul_left_dvd hdvd_n
      have hc0 : c ∣ m0 :=
        dvd_of_dvd_mul_pow_of_not_dvd p t m0 c hc_dvd hndvd_c
      have hcpos : 0 < c := by
        rcases Nat.eq_zero_or_pos c with rfl | hpos
        · simp_all
        · exact hpos
      rw [hdc]
      constructor
      · exact Nat.mem_divisors.mpr ⟨hc0, hm00⟩
      · exact hndvd_c
    · intro d1 h1 d2 h2 h12
      simp only [Finset.mem_filter] at h1 h2
      obtain ⟨⟨hm1, hd1⟩, _⟩ := h1
      obtain ⟨⟨hm2, hd2⟩, _⟩ := h2
      obtain ⟨c1, hc1⟩ := hd1
      obtain ⟨c2, hc2⟩ := hd2
      have e1 : d1 / p = c1 := by
        rw [hc1]
        exact Nat.mul_div_cancel_left c1 hp0
      have e2 : d2 / p = c2 := by
        rw [hc2]
        exact Nat.mul_div_cancel_left c2 hp0
      rw [e1, e2] at h12
      rw [hc1, hc2, h12]
    · intro e he
      rw [Finset.mem_filter] at he
      obtain ⟨hmem, hndvd⟩ := he
      have he0 : e ∣ m0 := Nat.dvd_of_mem_divisors hmem
      have hepos : 0 < e := by
        rcases Nat.eq_zero_or_pos e with rfl | hpos
        · simp_all
        · exact hpos
      have hpe_dvd : p * e ∣ p ^ (t + 1) * m0 :=
        mul_dvd_pow_mul_of_dvd p t m0 e he0
      have hmem_n : p * e ∈ Nat.divisors (p ^ (t + 1) * m0) :=
        Nat.mem_divisors.mpr ⟨hpe_dvd, hn0⟩
      have hpdvd : p ∣ p * e := dvd_mul_right p e
      have hnsq : ¬ p * p ∣ p * e := by
        intro hsq
        have h : p ∣ e := by
          have hiff := (Nat.mul_dvd_mul_iff_left hp0).mp hsq
          exact hiff
        exact hndvd h
      refine ⟨p * e, ?_, ?_⟩
      · simp only [Finset.mem_filter]
        constructor
        · exact ⟨hmem_n, hpdvd⟩
        · exact hnsq
      · exact Nat.mul_div_cancel_left e hp0
    · intro d hd
      simp only [Finset.mem_filter] at hd
      obtain ⟨⟨hmem, hdvd⟩, hnsq⟩ := hd
      obtain ⟨c, hc⟩ := hdvd
      have hdc : d / p = c := by
        rw [hc]
        exact Nat.mul_div_cancel_left c hp0
      rw [hdc]
      have hndvd_c : ¬ p ∣ c := by
        intro hcp
        have hsq : p * p ∣ d := by
          rw [hc]
          exact Nat.mul_dvd_mul_left p hcp
        exact hnsq hsq
      have hdvd_n : d ∣ p ^ (t + 1) * m0 := Nat.dvd_of_mem_divisors hmem
      have hc_dvd : c ∣ p ^ (t + 1) * m0 := by
        rw [hc] at hdvd_n
        exact dvd_of_mul_left_dvd hdvd_n
      have hc0 : c ∣ m0 :=
        dvd_of_dvd_mul_pow_of_not_dvd p t m0 c hc_dvd hndvd_c
      have hcpos : 0 < c := by
        rcases Nat.eq_zero_or_pos c with rfl | hpos
        · simp_all
        · exact hpos
      have hmu : (⇑ArithmeticFunction.moebius d)
          = ⇑ArithmeticFunction.moebius (p * c) := by
        rw [hc]
      have hdiv : (p ^ (t + 1) * m0) / d = p ^ t * (m0 / c) := by
        have hpe : d = p * c := hc
        rw [hpe]
        exact div_pow_mul_prime_eq p t m0 c hp0 hcpos hc0
      rw [hmu, hdiv]
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((Nat.divisors (p ^ (t + 1) * m0)).filter (fun d => p ∣ d))
    (fun d => p * p ∣ d)
    (fun d => (⇑ArithmeticFunction.moebius d) *
      a ((p ^ (t + 1) * m0) / d))
  have hS2neg : (∑ e ∈ (Nat.divisors m0).filter (fun e => ¬ p ∣ e),
        (⇑ArithmeticFunction.moebius (p * e)) * a (p ^ t * (m0 / e)))
      = ∑ e ∈ (Nat.divisors m0).filter (fun e => ¬ p ∣ e),
        (⇑ArithmeticFunction.moebius e) * (-a (p ^ t * (m0 / e))) := by
    apply Finset.sum_congr rfl
    intro e he
    have hndvd : ¬ p ∣ e := (Finset.mem_filter.mp he).2
    have hmu := moebius_prime_mul hndvd
    rw [hmu, neg_mul, mul_neg]
  have hcombine : (∑ d ∈ Nat.divisors (p ^ (t + 1) * m0),
        (⇑ArithmeticFunction.moebius d) * a ((p ^ (t + 1) * m0) / d))
      = (∑ d ∈ (Nat.divisors (p ^ (t + 1) * m0)).filter (fun d => ¬ p ∣ d),
        (⇑ArithmeticFunction.moebius d) * a ((p ^ (t + 1) * m0) / d))
        + (∑ d ∈ ((Nat.divisors (p ^ (t + 1) * m0)).filter
          (fun d => p ∣ d)).filter (fun d => ¬ p * p ∣ d),
          (⇑ArithmeticFunction.moebius d) * a ((p ^ (t + 1) * m0) / d)) := by
    have h1 : (∑ d ∈ Nat.divisors (p ^ (t + 1) * m0),
          (⇑ArithmeticFunction.moebius d) * a ((p ^ (t + 1) * m0) / d))
        = (∑ d ∈ (Nat.divisors (p ^ (t + 1) * m0)).filter (fun d => p ∣ d),
          (⇑ArithmeticFunction.moebius d) * a ((p ^ (t + 1) * m0) / d))
          + (∑ d ∈ (Nat.divisors (p ^ (t + 1) * m0)).filter (fun d => ¬ p ∣ d),
            (⇑ArithmeticFunction.moebius d) * a ((p ^ (t + 1) * m0) / d)) :=
      hsplit1.symm
    have h2 : (∑ d ∈ (Nat.divisors (p ^ (t + 1) * m0)).filter (fun d => p ∣ d),
          (⇑ArithmeticFunction.moebius d) * a ((p ^ (t + 1) * m0) / d))
        = (∑ d ∈ ((Nat.divisors (p ^ (t + 1) * m0)).filter
            (fun d => p ∣ d)).filter (fun d => p * p ∣ d),
            (⇑ArithmeticFunction.moebius d) * a ((p ^ (t + 1) * m0) / d))
          + (∑ d ∈ ((Nat.divisors (p ^ (t + 1) * m0)).filter
            (fun d => p ∣ d)).filter (fun d => ¬ p * p ∣ d),
            (⇑ArithmeticFunction.moebius d) * a ((p ^ (t + 1) * m0) / d)) :=
      hsplit2.symm
    rw [h1, h2, hS0, zero_add, add_comm]
  rw [hcombine, hS1, hS2, hS2neg]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- **Binomial-power sequences are Dold realizable.** Let $r \ge 1$ and $s \ge 0$ be integers and
let $A_{r,s}(n) = \sum_{k=0}^{n} \binom{n}{k}^r \binom{n+k}{k}^s$. Then the integer sequence
$(A_{r,s}(n))_{n \ge 0}$ is Dold realizable: for every integer $n \ge 1$, the sum
$\sum_{d \mid n} \mu(d)\, A_{r,s}(n/d)$ over the positive divisors $d$ of $n$, where $\mu$ is
the Möbius function, is non-negative and divisible by $n$.

Source: Zhang 2024, J. Integer Seq. 27, Article 24.3.3, Theorem 1.13.
Proves `Wanted` entry `binomial_power_sequence_dold_realizable`.
-/
theorem binomial_power_sequence_dold_realizable : ∀ r s : ℕ, 0 < r → doldRealizable
  (fun n => ((binomialPowerSeq r s n : ℕ) : ℤ)) := by
  intro r s hr n hn
  constructor
  · have hppdvd : ∀ p t : ℕ, Nat.Prime p → p ^ (t + 1) ∣ n →
        ((p ^ (t + 1) : ℕ) : ℤ) ∣ ∑ d ∈ Nat.divisors n,
          (⇑ArithmeticFunction.moebius d) * ((binomialPowerSeq r s (n / d) : ℕ) : ℤ) := by
      intro p t hp hdiv
      have : Fact (Nat.Prime p) := ⟨hp⟩
      obtain ⟨m, rfl⟩ := hdiv
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hn
        · exact h
      have hreorg := moebius_sum_reorg p t m hm0
        (fun n => ((binomialPowerSeq r s n : ℕ) : ℤ))
      have hsum : (∑ d ∈ Nat.divisors (p ^ (t + 1) * m),
            (⇑ArithmeticFunction.moebius d) *
              ((binomialPowerSeq r s ((p ^ (t + 1) * m) / d) : ℕ) : ℤ))
          = ∑ e ∈ (Nat.divisors m).filter (fun e => ¬ p ∣ e),
            (⇑ArithmeticFunction.moebius e) *
              ((((binomialPowerSeq r s (p ^ (t + 1) * (m / e)) : ℕ)) : ℤ) -
                (((binomialPowerSeq r s (p ^ t * (m / e)) : ℕ)) : ℤ)) := hreorg
      rw [hsum]
      apply Finset.dvd_sum
      intro e _
      have hmod := binomialPowerSeq_prime_pow_modEq p t r s (m / e) hr
      have hI : (((binomialPowerSeq r s (p ^ (t + 1) * (m / e)) : ℕ)) : ℤ) ≡
          (((binomialPowerSeq r s (p ^ t * (m / e)) : ℕ)) : ℤ)
          [ZMOD ((p ^ (t + 1) : ℕ) : ℤ)] :=
        Int.natCast_modEq_iff.mpr hmod
      exact dvd_mul_of_dvd_right (Int.modEq_iff_dvd.mp hI.symm) _
    have hne : n ≠ 0 := by omega
    by_cases hS0 : (∑ d ∈ Nat.divisors n,
        (⇑ArithmeticFunction.moebius d) * ((binomialPowerSeq r s (n / d) : ℕ) : ℤ)) = 0
    · rw [hS0]
      exact dvd_zero _
    · have hSne : (∑ d ∈ Nat.divisors n,
          (⇑ArithmeticFunction.moebius d) *
            ((binomialPowerSeq r s (n / d) : ℕ) : ℤ)).natAbs ≠ 0 := by
        intro hcon
        exact hS0 (Int.natAbs_eq_zero.mp hcon)
      have hndvd : n ∣ (∑ d ∈ Nat.divisors n,
          (⇑ArithmeticFunction.moebius d) *
            ((binomialPowerSeq r s (n / d) : ℕ) : ℤ)).natAbs := by
        rw [← Nat.factorization_prime_le_iff_dvd hne hSne]
        intro q hq
        by_cases hk : n.factorization q = 0
        · rw [hk]
          exact zero_le
        · obtain ⟨t, ht⟩ : ∃ t, n.factorization q = t + 1 :=
            ⟨n.factorization q - 1, by omega⟩
          rw [ht]
          have hqp : q ^ (t + 1) ∣ n := by
            rw [← ht]
            exact Nat.ordProj_dvd n q
          have hz := hppdvd q t hq hqp
          have hq2 : q ^ (t + 1) ∣ (∑ d ∈ Nat.divisors n,
              (⇑ArithmeticFunction.moebius d) *
                ((binomialPowerSeq r s (n / d) : ℕ) : ℤ)).natAbs := by
            have h3 := Int.natAbs_dvd_natAbs.mpr hz
            rwa [Int.natAbs_natCast] at h3
          exact (hq.pow_dvd_iff_le_factorization hSne).mp hq2
      have hfin : ((n : ℤ)).natAbs ∣ (∑ d ∈ Nat.divisors n,
          (⇑ArithmeticFunction.moebius d) *
            ((binomialPowerSeq r s (n / d) : ℕ) : ℤ)).natAbs := by
        rw [Int.natAbs_natCast]
        exact hndvd
      exact Int.natAbs_dvd_natAbs.mp hfin
  · exact binomialPowerSeq_moebius_nonneg r s n hr hn

/-- **Dold congruences for binomial-power sequences.** Let $r \ge 1$ and $s \ge 0$ be integers
and let $A_{r,s}(m) = \sum_{k=0}^{m} \binom{m}{k}^r \binom{m+k}{k}^s$. Then for every integer
$n \ge 1$, $n$ divides $\sum_{d \mid n} \mu(d)\, A_{r,s}(n/d)$, where $\mu$ is the Möbius
function and $d$ runs over the positive divisors of $n$. -/
theorem binomialPowerSeq_dold_congruences (r s : ℕ) (hr : 0 < r) (n : ℕ)
    (hn : 0 < n) :
    (n : ℤ) ∣ ∑ d ∈ Nat.divisors n, (⇑ArithmeticFunction.moebius d) *
      ((binomialPowerSeq r s (n / d) : ℕ) : ℤ) :=
  doldRealizable_dvd (binomial_power_sequence_dold_realizable r s hr) n hn

/-- **Non-negativity of the Möbius transform of binomial-power sequences.** Let $r \ge 1$ and
$s \ge 0$ be integers and let $A_{r,s}(m) = \sum_{k=0}^{m} \binom{m}{k}^r \binom{m+k}{k}^s$.
Then for every integer $n \ge 1$, $\sum_{d \mid n} \mu(d)\, A_{r,s}(n/d) \ge 0$, where $\mu$
is the Möbius function and $d$ runs over the positive divisors of $n$. -/
theorem binomialPowerSeq_moebius_sum_nonneg (r s : ℕ) (hr : 0 < r) (n : ℕ)
    (hn : 0 < n) :
    0 ≤ ∑ d ∈ Nat.divisors n, (⇑ArithmeticFunction.moebius d) *
      ((binomialPowerSeq r s (n / d) : ℕ) : ℤ) :=
  doldRealizable_nonneg (binomial_power_sequence_dold_realizable r s hr) n hn

end
end MetaMathlibExt
