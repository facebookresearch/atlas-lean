/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Logic.Function.Iterate

/-! # Parity of binomial coefficients and Delannoy arrays -/

namespace MetaMathlibExt.DelannoyConstructions

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

end MetaMathlibExt.DelannoyConstructions
