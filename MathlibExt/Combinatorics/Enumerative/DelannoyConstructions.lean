/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Logic.Function.Iterate

/-! # Generalized Delannoy numbers and parity in Delannoy arrays -/

namespace MetaMathlibExt.DelannoyConstructions

open Finset

/-- **Generalized Delannoy number with upper index.** For natural numbers $k$, $m$ and $n$, the
generalized Delannoy number $D^k(m, n)$ is the natural number

$$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}.$$

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Section 1 (definition of `D^k(m, n)`). -/
@[expose] public def genDelannoyUpper (k m n : ℕ) : ℕ :=
  ∑ j ∈ range (n + 1), (m + n + k - j).choose (n + k) * n.choose j

/-- **Lower generalized Delannoy number.** For natural numbers $k$, $m$ and $n$, the generalized
Delannoy number $D_k(m, n)$ is
$$D_k(m, n) = \sum_{j=0}^{n} \binom{m + n - k - j}{n - k} \binom{n}{j},$$
where each subtraction is truncated at $0$. The definition is intended for $m, n \ge k$, where
no truncation occurs.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Section 1 (definition of `D_k(m, n)`). -/
@[expose] public def genDelannoyLower (k m n : ℕ) : ℕ :=
  ∑ j ∈ range (n + 1), (m + n - k - j).choose (n - k) * n.choose j

/-- **An upper generalized Delannoy number equal to $13$.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. Then $D^0(2, 2) = 13$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Table 1. -/
public theorem genDelannoyUpper_zero_two_two : genDelannoyUpper 0 2 2 = 13 := by decide

/-- **An upper generalized Delannoy number equal to $44$.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. Then $D^1(3, 2) = 44$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Table 1. -/
public theorem genDelannoyUpper_one_three_two : genDelannoyUpper 1 3 2 = 44 := by decide

/-- **A value of the lower generalized Delannoy number.** The lower generalized Delannoy number
$D_1(2, 2)$ equals $8$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Section 1
(central theorem `D_k(m, n) = 2^k D^k(n - k, m - k)`). -/
public theorem genDelannoyLower_one_two_two : genDelannoyLower 1 2 2 = 8 := by decide

/-- **The lower and upper generalized Delannoy numbers agree at index zero.** For natural
numbers $k$, $m$ and $n$, let
$D_k(m, n) = \sum_{j=0}^{n} \binom{m + n - k - j}{n - k} \binom{n}{j}$ (with subtraction
truncated at $0$) and
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ be the lower
and upper generalized Delannoy numbers. Then $D_0(m, n) = D^0(m, n)$ for all natural numbers
$m$ and $n$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Section 1. -/
public theorem genDelannoyLower_zero (m n : ℕ) :
    genDelannoyLower 0 m n = genDelannoyUpper 0 m n := by
  simp [genDelannoyLower, genDelannoyUpper]

/-- **Horizontal sum identity for the upper generalized Delannoy numbers.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. For all natural numbers $k$, $m$ and $n$,
$D^k(m, n) + D^k(m, n + 1) = 2 D^{k+1}(m, n)$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 3
(`jis-2024-24.1.8-thm-3`). -/
public theorem genDelannoyUpper_add_succ_right (k m n : ℕ) :
    genDelannoyUpper k m n + genDelannoyUpper k m (n + 1) = 2 * genDelannoyUpper (k + 1) m n := by
  have hsplit : genDelannoyUpper k m (n + 1) = genDelannoyUpper (k + 1) m n +
      ∑ j ∈ range (n + 1), (m + n + k - j).choose (n + k + 1) * n.choose j := by
    simpa only [genDelannoyUpper, ← Nat.add_assoc, Nat.add_right_comm _ 1 k,
      Nat.add_sub_add_right, Nat.cast_id, Nat.mul_comm] using
      sum_choose_succ_mul (fun j _ ↦ (m + n + k + 1 - j).choose (n + k + 1)) n
  rw [hsplit, add_left_comm, two_mul]
  congr 1
  unfold genDelannoyUpper
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [← Nat.add_mul, ← Nat.choose_succ_succ']
  have hj' := mem_range.mp hj
  congr 2
  omega

/-- **Vertical sum identity for the upper generalized Delannoy numbers.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. For all natural numbers $k$, $m$ and $n$ with $k \ge 1$,
$D^k(m, n) + D^k(m + 1, n) = D^{k-1}(m + 1, n + 1)$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 4
(`jis-2024-24.1.8-thm-4`). -/
public theorem genDelannoyUpper_add_succ_left (k m n : ℕ) (hk : 1 ≤ k) :
    genDelannoyUpper k m n + genDelannoyUpper k (m + 1) n =
      genDelannoyUpper (k - 1) (m + 1) (n + 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [add_comm (genDelannoyUpper (s + 1) m n)]
  simp only [Nat.add_sub_cancel]
  have hsplit := sum_choose_succ_mul
    (fun j _ ↦ (m + n + (s + 1) + 1 - j).choose (n + (s + 1))) n
  have htop : m + 1 + n + (s + 1) = m + n + (s + 1) + 1 := by omega
  have htop' : m + 1 + (n + 1) + s = m + n + (s + 1) + 1 := by omega
  have hbot : n + 1 + s = n + (s + 1) := by omega
  simpa only [genDelannoyUpper, htop, htop', hbot, Nat.add_sub_add_right, Nat.cast_id,
    Nat.mul_comm] using hsplit.symm

/-- **Horizontal difference identity for the upper generalized Delannoy numbers.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. For all natural numbers $k$, $m$ and $n$ with $m \ge 1$,
$D^k(m, n + 1) - D^k(m, n) = 2 D^{k+1}(m - 1, n)$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Corollary 5
(`jis-2024-24.1.8-cor-5`). -/
public theorem genDelannoyUpper_succ_right_sub (k m n : ℕ) (hm : 1 ≤ m) :
    (genDelannoyUpper k m (n + 1) : ℤ) - genDelannoyUpper k m n =
      2 * genDelannoyUpper (k + 1) (m - 1) n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have hpascal : genDelannoyUpper (k + 1) (m + 1) n =
      genDelannoyUpper k (m + 1) n + genDelannoyUpper (k + 1) m n := by
    unfold genDelannoyUpper
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' := mem_range.mp hj
    have htop : m + n + (k + 1) - j = m + 1 + n + k - j := by omega
    have hsucc : m + 1 + n + (k + 1) - j = m + 1 + n + k - j + 1 := by omega
    rw [hsucc, htop, ← Nat.add_assoc n k 1, ← Nat.add_mul, Nat.choose_succ_succ']
  have hsum := genDelannoyUpper_add_succ_right k (m + 1) n
  simp only [Nat.add_sub_cancel]
  omega

/-- **Parity of a sum of adjacent binomial coefficients.** For all natural numbers $n$ and $k$
with $k \ge 1$, $\binom{n}{k} + \binom{n+1}{k} \equiv \binom{n}{k-1} \pmod 2$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Lemma 15
(`jis-2024-24.1.8-lem-15`). -/
public theorem choose_add_choose_succ_modEq_two (n k : ℕ) (hk : 1 ≤ k) :
    n.choose k + (n + 1).choose k ≡ n.choose (k - 1) [MOD 2] := by
  rw [Nat.choose_succ_left n k hk, ← add_assoc, add_right_comm, ← Nat.two_mul]
  exact Nat.ModEq.modulus_mul_add

private def horizontalSum (S : ℕ → ℕ → ℤ) (m n : ℕ) : ℤ :=
  S m n + S m (n + 1)

-- Adjacent rows of a horizontal sum differ by twice the lower entry before summing.
private theorem iterate_horizontalSum_succ_row (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n)
    (i m n : ℕ) :
    horizontalSum^[i + 1] R (m + 1) n =
      horizontalSum^[i + 1] R m n + 2 * horizontalSum^[i] R (m + 1) n := by
  induction i generalizing n with
  | zero =>
    change R (m + 1) n + R (m + 1) (n + 1) = R m n + R m (n + 1) + 2 * R (m + 1) n
    rw [hR]
    omega
  | succ i ih =>
    have hn := ih n
    have hn' := ih (n + 1)
    simp only [Function.iterate_succ_apply', horizontalSum] at hn hn' ⊢
    omega

/-- **Rows of iterated horizontal sums of a Delannoy array agree mod 2.** Let $R(m, n)$, for
$m, n \in \mathbb{N}$, be integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for all
$m, n$. For an array $S$ let $(HS)(m, n) = S(m, n) + S(m, n+1)$, and write $R^i = H^i R$ for the
$i$-fold horizontal sum. Then for every $i \ge 1$ and all $m, m', n \in \mathbb{N}$,
$R^i(m, n) \equiv R^i(m', n) \pmod 2$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Corollary 14
(`jis-2024-24.1.8-cor-14`). -/
public theorem delannoyArray_horizontalSum_rows_modEq (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n) (i : ℕ) (hi : 1 ≤ i)
    (m m' n : ℕ) :
    (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[i] R m n ≡
      (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[i] R m' n [ZMOD 2] := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
  have row_zero (a : ℕ) : horizontalSum^[j + 1] R a n ≡ horizontalSum^[j + 1] R 0 n [ZMOD 2] := by
    induction a with
    | zero => rfl
    | succ a ih => rwa [iterate_horizontalSum_succ_row R hR j a n, Int.add_modulus_mul_modEq_iff]
  exact (row_zero m).trans (row_zero m').symm

private theorem iterate_horizontalSum_seed (R : ℕ → ℕ → ℤ) (k : ℕ)
    (hseed : ∀ n, R 0 n = (k + n).choose k) (j : ℕ) (hj : j ≤ k) (n : ℕ) :
    horizontalSum^[j] R 0 n ≡ ((k + n).choose (k - j) : ℤ) [ZMOD 2] := by
  induction j generalizing n with
  | zero => simp [hseed]
  | succ j ih =>
    have h := ih (by omega) n
    have h' := ih (by omega) (n + 1)
    rw [Function.iterate_succ_apply']
    apply (h.add h').trans
    have hchoose := choose_add_choose_succ_modEq_two (k + n) (k - j) (by omega)
    simpa [Nat.add_assoc, Nat.sub_sub] using Int.natCast_modEq_iff.mpr hchoose

/-- **Parity of iterated horizontal sums of a Delannoy array with binomial seeds.** Let $R(m, n)$,
for $m, n \in \mathbb{N}$, be integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for
all $m, n$. For an array $S$ let $(HS)(m, n) = S(m, n) + S(m, n+1)$, and write $R^i = H^i R$ for
the $i$-fold horizontal sum, so $R^0 = R$. Let $k \in \mathbb{N}$ and suppose
$R(0, n) = \binom{k+n}{k}$ for all $n$; the values $R(m, 0)$ for $m \ge 1$ are arbitrary. Then
every entry of $R^{k+1}$ is even, and for every $j \le k$ some entry of $R^j$ is odd.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Lemma 16
(`jis-2024-24.1.8-lem-16`). -/
public theorem delannoyArray_binomial_seeds_parity (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n) (k : ℕ)
    (hseed : ∀ n, R 0 n = (k + n).choose k) :
    (∀ m n, (2 : ℤ) ∣ (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[k + 1] R m n) ∧
      ∀ j ≤ k, ∃ m n,
        ¬ (2 : ℤ) ∣ (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[j] R m n := by
  have hlast (n : ℕ) : horizontalSum^[k] R 0 n ≡ 1 [ZMOD 2] := by
    simpa using iterate_horizontalSum_seed R k hseed k le_rfl n
  constructor
  · intro m n
    change 2 ∣ horizontalSum^[k + 1] R m n
    induction m with
    | zero =>
      rw [Function.iterate_succ_apply']
      have h := (hlast n).add (hlast (n + 1))
      exact h.dvd_iff.mpr (by decide)
    | succ m ih =>
      rw [iterate_horizontalSum_succ_row R hR k m n]
      exact Int.dvd_add ih (dvd_mul_right ..)
  · intro j hj
    change ∃ m n, ¬ (2 : ℤ) ∣ horizontalSum^[j] R m n
    induction hj using Nat.decreasingInduction with
    | self =>
      refine ⟨0, 0, ?_⟩
      rw [(hlast 0).dvd_iff]
      decide
    | of_succ j _ ih =>
      obtain ⟨m, n, hn⟩ := ih
      rw [Function.iterate_succ_apply'] at hn
      by_cases h : (2 : ℤ) ∣ horizontalSum^[j] R m n
      · exact ⟨m, n + 1, fun h' => hn (Int.dvd_add h h')⟩
      · exact ⟨m, n, h⟩

/-- **First horizontal sums of a Delannoy array with binomial seeds.** Let $R(m, n)$, for
$m, n \in \mathbb{N}$, be integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for all
$m, n$. Let $k \ge 1$ and suppose $R(0, n) = \binom{k+n}{k}$ for all $n$. Then for all $m$ and
$n$, $R(m, n) + R(m, n+1) \equiv \binom{k+n}{k-1} \pmod 2$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 17
(`jis-2024-24.1.8-thm-17`). -/
public theorem delannoyArray_binomial_seeds_horizontalSum_modEq (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n) (k : ℕ) (hk : 1 ≤ k)
    (hseed : ∀ n, R 0 n = (k + n).choose k) (m n : ℕ) :
    R m n + R m (n + 1) ≡ (k + n).choose (k - 1) [ZMOD 2] := by
  exact (delannoyArray_horizontalSum_rows_modEq R hR 1 le_rfl m 0 n).trans
    (iterate_horizontalSum_seed R k hseed 1 hk n)

end MetaMathlibExt.DelannoyConstructions
