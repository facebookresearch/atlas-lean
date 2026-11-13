/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.BAryBinomialCoefficient
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Digits.Lemmas

@[expose] public section

namespace MetaMathlibExt

/-! # Symmetry and Pascal recurrence for b-ary binomial coefficients
-/

/-- **Digit-product formula for $b$-ary binomial coefficients.** Let $b \ge 2$ and let $n$, $k$
and $L$ be natural numbers with $n < b^L$ and $k < b^L$. Then the $b$-ary binomial coefficient
$\binom{n}{k}_b$ equals
$$\prod_{i=0}^{L-1} \binom{\lfloor n / b^i \rfloor \bmod b}{\lfloor k / b^i \rfloor \bmod b},$$
the product over the positions $i < L$ of the binomial coefficients of the $i$-th base-$b$ digits
of $n$ and $k$. -/
theorem bAryBinomialCoefficient_eq_prod_div_pow (b n k : ℕ) (hb : 2 ≤ b) {L : ℕ}
    (hn : n < b ^ L) (hk : k < b ^ L) :
    bAryBinomialCoefficient b n k hb =
      ∏ i ∈ Finset.range L, Nat.choose ((n / b ^ i) % b) ((k / b ^ i) % b) := by
  rw [bAryBinomialCoefficient_eq_prod_getD b n k hb ((Nat.digits_length_le_iff (by omega) n).mpr hn)
    ((Nat.digits_length_le_iff (by omega) k).mpr hk)]
  simp only [Nat.getD_digits _ _ hb]

private lemma lt_base_pow (b : ℕ) (hb : 2 ≤ b) (N L : ℕ) (h : N ≤ L) : N < b ^ L :=
  lt_of_lt_of_le (Nat.lt_pow_self (by omega)) (Nat.pow_le_pow_right (by omega) h)

private lemma tail_digits (b : ℕ) (hb : 2 ≤ b) (N K j : ℕ) (h : N + K ≤ j) :
    (N / b ^ j) % b = 0 ∧ (K / b ^ j) % b = 0 := by
  have h2 := Nat.lt_two_pow_self (n := j)
  have hpb : 2 ^ j ≤ b ^ j := Nat.pow_le_pow_left hb j
  have hN : N / b ^ j = 0 := Nat.div_eq_zero_iff.mpr (Or.inr (by omega))
  have hK : K / b ^ j = 0 := Nat.div_eq_zero_iff.mpr (Or.inr (by omega))
  simp [hN, hK]

private lemma bary_zero_right (b : ℕ) (hb : 2 ≤ b) (N : ℕ) :
    bAryBinomialCoefficient b N 0 hb = 1 := by
  rw [bAryBinomialCoefficient_eq_prod_div_pow b N 0 hb (lt_base_pow b hb N N le_rfl)
    (lt_base_pow b hb 0 N (Nat.zero_le N))]
  simp [Nat.choose_zero_right]

private lemma bary_split (b : ℕ) (hb : 2 ≤ b) (N K : ℕ) :
    bAryBinomialCoefficient b N K hb
      = Nat.choose (N % b) (K % b) * bAryBinomialCoefficient b (N / b) (K / b) hb := by
  have hNb := Nat.div_le_self N b
  have hKb := Nat.div_le_self K b
  rw [bAryBinomialCoefficient_eq_prod_div_pow b N K hb (lt_base_pow b hb N (N + K + 1) (by omega))
    (lt_base_pow b hb K (N + K + 1) (by omega)),
    bAryBinomialCoefficient_eq_prod_div_pow b (N / b) (K / b) hb
      (lt_base_pow b hb (N / b) (N + K) (by omega)) (lt_base_pow b hb (K / b) (N + K) (by omega)),
    Finset.prod_range_succ', mul_comm]
  simp only [pow_zero, Nat.div_one, pow_succ', ← Nat.div_div_eq_div_mul]

private lemma sub_decomp (b N K : ℕ) (hKN : K ≤ N) (hle : K % b ≤ N % b) :
    N - K = b * (N / b - K / b) + (N % b - K % b) := by
  have hN := Nat.div_add_mod N b
  have hK := Nat.div_add_mod K b
  have hq : K / b ≤ N / b := Nat.div_le_div_right hKN
  have hmul : b * (K / b) ≤ b * (N / b) := Nat.mul_le_mul_left b hq
  have hdist : b * (N / b) - b * (K / b) = b * (N / b - K / b) := by
    rw [Nat.mul_sub]
  have hthis : N - K = (b * (N / b) + N % b) - (b * (K / b) + K % b) := by
    rw [hN, hK]
  have hcalc : b * (N / b) + N % b - (b * (K / b) + K % b)
      = (b * (N / b) - b * (K / b)) + (N % b - K % b) := by omega
  rw [hthis, hcalc, hdist]

private lemma sub_mod_of_digit_le (b : ℕ) (hb : 0 < b) (N K : ℕ) (hKN : K ≤ N)
    (hle : K % b ≤ N % b) : (N - K) % b = N % b - K % b := by
  have hd := sub_decomp b N K hKN hle
  have hlt : N % b - K % b < b := lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ hb)
  rw [hd, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

private lemma sub_div_of_digit_le (b : ℕ) (hb : 0 < b) (N K : ℕ) (hKN : K ≤ N)
    (hle : K % b ≤ N % b) : (N - K) / b = N / b - K / b := by
  have hd := sub_decomp b N K hKN hle
  have hlt : N % b - K % b < b := lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ hb)
  have hz : (N % b - K % b) / b = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hlt)
  rw [hd, add_comm, Nat.add_mul_div_left _ _ hb, hz, zero_add]

private lemma digit_sub (b : ℕ) (hb : 2 ≤ b) :
    ∀ (i : ℕ) (N K : ℕ), K ≤ N → (∀ j, (K / b ^ j) % b ≤ (N / b ^ j) % b) →
      ((N - K) / b ^ i) % b = (N / b ^ i) % b - (K / b ^ i) % b := by
  have hb0 : 0 < b := by omega
  intro i
  induction i with
  | zero =>
    intro N K hKN hdig
    simp only [pow_zero, Nat.div_one]
    exact sub_mod_of_digit_le b hb0 N K hKN (by simpa using hdig 0)
  | succ i ih =>
    intro N K hKN hdig
    have e1 : b ^ (i + 1) = b * b ^ i := pow_succ' b i
    have hle0 : K % b ≤ N % b := by have h := hdig 0; simpa using h
    have hq : (N - K) / b = N / b - K / b :=
      sub_div_of_digit_le b hb0 N K hKN hle0
    have hKN' : K / b ≤ N / b := Nat.div_le_div_right hKN
    have hdig' : ∀ j, ((K / b) / b ^ j) % b ≤ ((N / b) / b ^ j) % b := by
      intro j
      have e2 : b ^ (j + 1) = b * b ^ j := pow_succ' b j
      have h := hdig (j + 1)
      rw [e2, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at h
      exact h
    rw [e1, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      ← Nat.div_div_eq_div_mul, hq]
    exact ih (N / b) (K / b) hKN' hdig'

private lemma bary_ne_zero_digits (b : ℕ) (hb : 2 ≤ b) (N K : ℕ)
    (h : bAryBinomialCoefficient b N K hb ≠ 0) (i : ℕ) :
    (K / b ^ i) % b ≤ (N / b ^ i) % b := by
  rw [bAryBinomialCoefficient_eq_prod_div_pow b N K hb (lt_base_pow b hb N (N + K + 1) (by omega))
    (lt_base_pow b hb K (N + K + 1) (by omega))] at h
  by_cases hle : (K / b ^ i) % b ≤ (N / b ^ i) % b
  · exact hle
  · exfalso
    have hlt : (N / b ^ i) % b < (K / b ^ i) % b := lt_of_not_ge hle
    rcases lt_or_ge i (N + K + 1) with hi | hi
    · have h0 : Nat.choose ((N / b ^ i) % b) ((K / b ^ i) % b) = 0 :=
        Nat.choose_eq_zero_of_lt hlt
      have hmem : i ∈ Finset.range (N + K + 1) := Finset.mem_range.mpr hi
      exact h (Finset.prod_eq_zero hmem h0)
    · obtain ⟨h1, h2⟩ := tail_digits b hb N K i (by omega)
      omega

private lemma bary_symm_of_digits (b : ℕ) (hb : 2 ≤ b) (N J : ℕ) (hJN : J ≤ N)
    (hdig : ∀ j, (J / b ^ j) % b ≤ (N / b ^ j) % b) :
    bAryBinomialCoefficient b N J hb = bAryBinomialCoefficient b N (N - J) hb := by
  have hdig2 : ∀ j, ((N - J) / b ^ j) % b = (N / b ^ j) % b - (J / b ^ j) % b :=
    fun j => digit_sub b hb j N J hJN hdig
  have hN := lt_base_pow b hb N N le_rfl
  rw [bAryBinomialCoefficient_eq_prod_div_pow b N J hb hN (lt_base_pow b hb J N hJN),
    bAryBinomialCoefficient_eq_prod_div_pow b N (N - J) hb hN
      (lt_base_pow b hb (N - J) N (by omega))]
  apply Finset.prod_congr rfl
  intro x _
  rw [hdig2 x]
  exact (Nat.choose_symm (hdig x)).symm

/-- **Symmetry of $b$-ary binomial coefficients.** Let $b \ge 2$ and write $\binom{n}{k}_b$ for
the $b$-ary binomial coefficient. For all natural numbers $k \le n$,
$\binom{n}{k}_b = \binom{n}{n-k}_b$. -/
theorem bAryBinomialCoefficient_symm (b n k : ℕ) (hb : 2 ≤ b) (hkn : k ≤ n) :
    bAryBinomialCoefficient b n k hb = bAryBinomialCoefficient b n (n - k) hb := by
  by_cases hzero : bAryBinomialCoefficient b n k hb = 0
  · have h2 : bAryBinomialCoefficient b n (n - k) hb = 0 := by
      by_contra hne
      have hdig := fun j => bary_ne_zero_digits b hb n (n - k) hne j
      have hle : n - k ≤ n := Nat.sub_le n k
      have heq := bary_symm_of_digits b hb n (n - k) hle hdig
      have hnk : n - (n - k) = k := Nat.sub_sub_self hkn
      rw [hnk] at heq
      exact hne (heq.trans hzero)
    rw [hzero, h2]
  · exact bary_symm_of_digits b hb n k hkn
      (fun j => bary_ne_zero_digits b hb n k hzero j)

private lemma pred_div_mod (b : ℕ) (hb : 2 ≤ b) (N : ℕ) (hN : 0 < N) (h : N % b ≠ 0) :
    (N - 1) / b = N / b ∧ (N - 1) % b = N % b - 1 := by
  have hb0 : 0 < b := by omega
  have h1b : 1 % b = 1 := Nat.mod_eq_of_lt (by omega)
  have h1d : 1 / b = 0 := Nat.div_eq_zero_iff.mpr (Or.inr (by omega))
  have hle1 : 1 % b ≤ N % b := by rw [h1b]; omega
  have hd := sub_decomp b N 1 hN hle1
  rw [h1d, Nat.sub_zero, h1b] at hd
  have hlt : N % b - 1 < b := lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ hb0)
  constructor
  · rw [hd, add_comm, Nat.add_mul_div_left _ _ hb0,
      Nat.div_eq_zero_iff.mpr (Or.inr hlt), zero_add]
  · rw [hd, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

private lemma pred_div_mod_zero (b : ℕ) (hb : 2 ≤ b) (N : ℕ) (hN : 0 < N)
    (h : N % b = 0) :
    (N - 1) / b = N / b - 1 ∧ (N - 1) % b = b - 1 := by
  have hb0 : 0 < b := by omega
  have hNN : N = b * (N / b) + N % b := (Nat.div_add_mod N b).symm
  have hQ' : 0 < N / b := by
    by_contra hc
    have hz : N / b = 0 := Nat.le_zero.mp (le_of_not_gt hc)
    rw [hz, h, Nat.mul_zero, Nat.add_zero] at hNN
    omega
  obtain ⟨Q, hQ⟩ : ∃ Q, N / b = Q + 1 := ⟨N / b - 1, by omega⟩
  have hmul : b * (Q + 1) = b * Q + b := by rw [mul_add, mul_one]
  have hdecomp : N - 1 = b * Q + (b - 1) := by
    rw [h, hQ, Nat.add_zero, hmul] at hNN
    omega
  have hlt : b - 1 < b := by omega
  have hQb : N / b - 1 = Q := by omega
  constructor
  · rw [hdecomp, add_comm, Nat.add_mul_div_left _ _ hb0,
      Nat.div_eq_zero_iff.mpr (Or.inr hlt), zero_add, hQb]
  · rw [hdecomp, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

private lemma bary_pascal_all (b : ℕ) (hb : 2 ≤ b) :
    ∀ N K : ℕ, K ≤ N → 0 < K → 0 < N → bAryBinomialCoefficient b N K hb ≠ 0 →
      bAryBinomialCoefficient b N K hb =
        bAryBinomialCoefficient b (N - 1) (K - 1) hb + bAryBinomialCoefficient b (N - 1) K hb := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro K hKN hK hN hne
    have hb0 : 0 < b := by omega
    have hdig : ∀ j, (K / b ^ j) % b ≤ (N / b ^ j) % b :=
      fun j => bary_ne_zero_digits b hb N K hne j
    have hnb : K % b ≤ N % b := by have h := hdig 0; simpa using h
    have eNK : bAryBinomialCoefficient b N K hb
        = Nat.choose (N % b) (K % b) * bAryBinomialCoefficient b (N / b) (K / b) hb :=
      bary_split b hb N K
    by_cases hmodN : N % b = 0
    · -- Case B: N has trailing zero in base b; use induction on the quotient.
      have hmodK0 : K % b = 0 := by omega
      have hN1 := pred_div_mod_zero b hb N hN hmodN
      have hK1 := pred_div_mod_zero b hb K hK hmodK0
      have hNb : 0 < N / b := by
        by_contra hc
        have hz : N / b = 0 := Nat.le_zero.mp (le_of_not_gt hc)
        have hNN : N = b * (N / b) + N % b := (Nat.div_add_mod N b).symm
        rw [hz, hmodN, Nat.mul_zero, Nat.add_zero] at hNN
        omega
      have hKb : 0 < K / b := by
        by_contra hc
        have hz : K / b = 0 := Nat.le_zero.mp (le_of_not_gt hc)
        have hKK : K = b * (K / b) + K % b := (Nat.div_add_mod K b).symm
        rw [hz, hmodK0, Nat.mul_zero, Nat.add_zero] at hKK
        omega
      have hF' : bAryBinomialCoefficient b (N / b) (K / b) hb ≠ 0 := by
        have h := hne
        rw [eNK, hmodN, hmodK0, Nat.choose_zero_right, one_mul] at h
        exact h
      have hlt : N / b < N := Nat.div_lt_self hN (by omega)
      have hle : K / b ≤ N / b := Nat.div_le_div_right hKN
      have hih := ih (N / b) hlt (K / b) hle hKb hNb hF'
      have e1 : bAryBinomialCoefficient b (N - 1) (K - 1) hb
          = bAryBinomialCoefficient b (N / b - 1) (K / b - 1) hb := by
        rw [bary_split b hb (N - 1) (K - 1), hN1.2, hK1.2, hN1.1, hK1.1,
          Nat.choose_self, one_mul]
      have e2 : bAryBinomialCoefficient b (N - 1) K hb
          = bAryBinomialCoefficient b (N / b - 1) (K / b) hb := by
        rw [bary_split b hb (N - 1) K, hN1.2, hN1.1, hmodK0,
          Nat.choose_zero_right, one_mul]
      rw [eNK, hmodN, hmodK0, Nat.choose_zero_right, one_mul, e1, e2]
      exact hih
    · -- Case A: lowest digit of N is nonzero.
      have hN1 := pred_div_mod b hb N hN hmodN
      by_cases hmodK : K % b = 0
      · -- A2: K has trailing zero; first summand vanishes.
        have hK1 := pred_div_mod_zero b hb K hK hmodK
        have e1 : bAryBinomialCoefficient b (N - 1) (K - 1) hb = 0 := by
          rw [bary_split b hb (N - 1) (K - 1), hN1.2, hK1.2, hN1.1, hK1.1]
          have hlt2 : N % b - 1 < b - 1 := by
            have hm := Nat.mod_lt N hb0
            omega
          rw [Nat.choose_eq_zero_of_lt hlt2, zero_mul]
        have e2 : bAryBinomialCoefficient b (N - 1) K hb
            = bAryBinomialCoefficient b (N / b) (K / b) hb := by
          rw [bary_split b hb (N - 1) K, hN1.2, hN1.1, hmodK,
            Nat.choose_zero_right, one_mul]
        rw [eNK, e1, e2, hmodK, Nat.choose_zero_right, one_mul, zero_add]
      · -- A1: ordinary Pascal on the lowest digits.
        have hK1 := pred_div_mod b hb K hK hmodK
        have e1 : bAryBinomialCoefficient b (N - 1) (K - 1) hb
            = Nat.choose (N % b - 1) (K % b - 1) *
              bAryBinomialCoefficient b (N / b) (K / b) hb := by
          rw [bary_split b hb (N - 1) (K - 1), hN1.2, hK1.2, hN1.1, hK1.1]
        have e2 : bAryBinomialCoefficient b (N - 1) K hb
            = Nat.choose (N % b - 1) (K % b) * bAryBinomialCoefficient b (N / b) (K / b) hb := by
          rw [bary_split b hb (N - 1) K, hN1.2, hN1.1]
        have hfin : Nat.choose (N % b) (K % b) * bAryBinomialCoefficient b (N / b) (K / b) hb
            = Nat.choose (N % b - 1) (K % b - 1) * bAryBinomialCoefficient b (N / b) (K / b) hb
            + Nat.choose (N % b - 1) (K % b) * bAryBinomialCoefficient b (N / b) (K / b) hb := by
          generalize hA : N % b - 1 = A
          generalize hB : K % b - 1 = B
          have hNA : N % b = A + 1 := by omega
          have hKA : K % b = B + 1 := by omega
          rw [hNA, hKA, Nat.choose_succ_succ, add_mul]
        rw [eNK, e1, e2]
        exact hfin

/-- **Pascal's recurrence for $b$-ary binomial coefficients.** Let $b \ge 2$ and write
$\binom{n}{k}_b$ for the $b$-ary binomial coefficient. For all natural numbers $n$ and $k$ with
$0 < k \le n$ and $\binom{n}{k}_b \ne 0$,
$\binom{n}{k}_b = \binom{n-1}{k-1}_b + \binom{n-1}{k}_b$. -/
theorem bAryBinomialCoefficient_pascal (b n k : ℕ) (hb : 2 ≤ b) (hk : 0 < k) (hkn : k ≤ n)
    (hne : bAryBinomialCoefficient b n k hb ≠ 0) :
    bAryBinomialCoefficient b n k hb =
      bAryBinomialCoefficient b (n - 1) (k - 1) hb + bAryBinomialCoefficient b (n - 1) k hb :=
  bary_pascal_all b hb n k hkn hk (by omega) hne

private lemma bary_prod_eq (b : ℕ) (hb : 2 ≤ b) (M J : ℕ) :
    ∏ i ∈ Finset.range (M + J + 1), Nat.choose ((M / b ^ i) % b) ((J / b ^ i) % b)
      = bAryBinomialCoefficient b M J hb :=
  (bAryBinomialCoefficient_eq_prod_div_pow b M J hb (lt_base_pow b hb M _ (by omega))
    (lt_base_pow b hb J _ (by omega))).symm

/--
**Symmetry and Pascal's recurrence for $b$-ary binomial coefficients.** Let $b \ge 2$. For a
natural number $m$ write $m_i = \lfloor m / b^i \rfloor \bmod b$ for its $i$-th base-$b$ digit.
For integers $m$ and $j$, let $C_b(m, j) = \prod_{i=0}^{m+j} \binom{m_i}{j_i}$ if $m \ge 0$ and
$j \ge 0$, and $C_b(m, j) = 0$ otherwise. Then for all integers $n$ and $k$ with $0 < n$ and
$0 \le k \le n$, we have $C_b(n, k) = C_b(n, n - k)$, and if $C_b(n, k) \ne 0$ then
$C_b(n, k) = C_b(n - 1, k - 1) + C_b(n - 1, k)$.

Proves `Wanted` entry `baryBinomial_symmetry_and_pascal`.

Source: Lin Jiu and Christophe Vignat, "On Binomial Identities in Arbitrary
Bases," Journal of Integer Sequences 19 (2016), Article 16.5.5, Theorem
(Symmetry and recurrence), equation (label `eq:recurrence`), lines 432–445,
https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu4.tex
-/
theorem baryBinomial_symmetry_and_pascal
    (b : ℕ) (hb : 2 ≤ b) (n k : ℤ) (hn : 0 < n) (hk : 0 ≤ k) (hkn : k ≤ n) :
    let baryBinomial : ℤ → ℤ → ℕ := fun m j =>
      if 0 ≤ m ∧ 0 ≤ j then
        let m' := m.toNat
        let j' := j.toNat
        ∏ i ∈ Finset.range (m' + j' + 1),
          Nat.choose ((m' / b ^ i) % b) ((j' / b ^ i) % b)
      else
        0
    baryBinomial n k = baryBinomial n (n - k) ∧
      (baryBinomial n k ≠ 0 →
        baryBinomial n k =
          baryBinomial (n - 1) (k - 1) + baryBinomial (n - 1) k) := by
  intro bb
  have hbb : bb = fun m j : ℤ =>
      if 0 ≤ m ∧ 0 ≤ j then
        let m' := m.toNat
        let j' := j.toNat
        ∏ i ∈ Finset.range (m' + j' + 1),
          Nat.choose ((m' / b ^ i) % b) ((j' / b ^ i) % b)
      else
        0 := rfl
  rw [hbb]
  simp only []
  obtain ⟨N, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn.le).symm⟩
  obtain ⟨K, rfl⟩ : ∃ m : ℕ, k = m := ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
  have hN : 0 < N := by omega
  have hKN : K ≤ N := by exact_mod_cast hkn
  have c1 : 0 ≤ (↑N : ℤ) ∧ 0 ≤ (↑K : ℤ) := by
    constructor <;> omega
  have c2 : 0 ≤ (↑N : ℤ) ∧ 0 ≤ (↑N : ℤ) - ↑K := ⟨by omega, sub_nonneg.mpr hkn⟩
  have hsub : ((↑N : ℤ) - ↑K).toNat = N - K := by
    rw [← Int.natCast_sub hKN, Int.toNat_natCast]
  refine ⟨?_, ?_⟩
  · rw [ite_eq_left c1, ite_eq_left c2]
    simp only [Int.toNat_natCast, hsub, bary_prod_eq b hb]
    exact bAryBinomialCoefficient_symm b N K hb hKN
  · intro hne
    rw [ite_eq_left c1] at hne ⊢
    simp only [Int.toNat_natCast, bary_prod_eq b hb] at hne ⊢
    by_cases hK0 : K = 0
    · subst hK0
      have cn1 : (0 : ℤ) ≤ ↑N - 1 := by
        have h1 : (1 : ℤ) ≤ ↑N := by omega
        omega
      have hneg : ¬ (0 : ℤ) ≤ ((0 : ℕ) : ℤ) - 1 := by decide
      rw [ite_eq_right (fun h => hneg h.2)]
      have cp : 0 ≤ (↑N : ℤ) - 1 ∧ 0 ≤ ((0 : ℕ) : ℤ) := ⟨cn1, by omega⟩
      rw [ite_eq_left cp]
      rw [bary_zero_right b hb, bary_zero_right b hb, zero_add]
    · have hKpos : 0 < K := Nat.pos_of_ne_zero hK0
      have cn1 : (0 : ℤ) ≤ ↑N - 1 := by
        have h1 : (1 : ℤ) ≤ ↑N := by omega
        omega
      have ck1 : (0 : ℤ) ≤ ↑K - 1 := by
        have h1 : (1 : ℤ) ≤ ↑K := by omega
        omega
      have cp1 : 0 ≤ (↑N : ℤ) - 1 ∧ 0 ≤ (↑K : ℤ) - 1 := ⟨cn1, ck1⟩
      have cp2 : 0 ≤ (↑N : ℤ) - 1 ∧ 0 ≤ (↑K : ℤ) := ⟨cn1, by omega⟩
      rw [ite_eq_left cp1, ite_eq_left cp2]
      have hNm1 : ((↑N : ℤ) - 1).toNat = N - 1 := by
        have h1 : ((N - 1 : ℕ) : ℤ) = ↑N - 1 := by
          rw [Int.natCast_sub hN, Int.natCast_one]
        rw [← h1, Int.toNat_natCast]
      have hKm1 : ((↑K : ℤ) - 1).toNat = K - 1 := by
        have h1 : ((K - 1 : ℕ) : ℤ) = ↑K - 1 := by
          rw [Int.natCast_sub hKpos, Int.natCast_one]
        rw [← h1, Int.toNat_natCast]
      rw [hNm1, hKm1]
      exact bAryBinomialCoefficient_pascal b N K hb hKpos hKN hne

end MetaMathlibExt
