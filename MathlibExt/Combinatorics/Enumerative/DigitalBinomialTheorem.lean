/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Star

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

/-! # Digital binomial theorem (carry-free expansion)
-/

/-- **Binary digit sum.** For a natural number $n$, the binary digit sum $s(n)$ is the sum of the
digits of $n$ in base $2$, that is, the number of ones in the binary expansion of $n$. -/
def binDigitSum (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- **Binary digit sum of zero.** The binary digit sum of $0$ is $0$. -/
@[simp]
theorem binDigitSum_zero : binDigitSum 0 = 0 := by
  simp [binDigitSum, Nat.digits_zero]

private theorem binDigitSum_rec (n : ℕ) (hn : n ≠ 0) :
    binDigitSum n = n % 2 + binDigitSum (n / 2) := by
  unfold binDigitSum
  rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hn), List.sum_cons]

/-- **Binary digit sum of an even number.** For every natural number $k$, the binary digit sum of
$2k$ equals the binary digit sum of $k$: doubling appends the binary digit $0$. -/
@[simp]
theorem binDigitSum_two_mul (k : ℕ) : binDigitSum (2 * k) = binDigitSum k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [binDigitSum_rec _ (by omega), show (2 * k) % 2 = 0 by omega,
      show (2 * k) / 2 = k by omega, Nat.zero_add]

/-- **Binary digit sum of an odd number.** For every natural number $k$, the binary digit sum of
$2k + 1$ is one more than the binary digit sum of $k$: the binary expansion of $2k + 1$ is that
of $k$ followed by the digit $1$. -/
@[simp]
theorem binDigitSum_two_mul_add_one (k : ℕ) :
    binDigitSum (2 * k + 1) = binDigitSum k + 1 := by
  rw [binDigitSum_rec _ (by omega), show (2 * k + 1) % 2 = 1 by omega,
    show (2 * k + 1) / 2 = k by omega]
  omega

/-- **Binary digit sum of one.** The binary digit sum of $1$ is $1$. -/
@[simp]
theorem binDigitSum_one : binDigitSum 1 = 1 := by
  simpa using binDigitSum_two_mul_add_one 0

private theorem binDigitSum_succ_le (u : ℕ) :
    binDigitSum (u + 1) ≤ binDigitSum u + 1 := by
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    obtain ⟨t, rfl | rfl⟩ : ∃ t, u = 2 * t ∨ u = 2 * t + 1 := ⟨u / 2, by omega⟩
    · rw [binDigitSum_two_mul_add_one, binDigitSum_two_mul]
    · have he : 2 * t + 1 + 1 = 2 * (t + 1) := by omega
      rw [he, binDigitSum_two_mul, binDigitSum_two_mul_add_one]
      have iht := ih t (by omega)
      omega

private theorem binDigitSum_add_le (n a b : ℕ) (hab : a + b = n) :
    binDigitSum n ≤ binDigitSum a + binDigitSum b := by
  revert a b hab
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab
    rcases eq_or_ne n 0 with hn0 | hn0
    · subst hn0
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
      simp [binDigitSum_zero]
    · obtain ⟨r, rfl | rfl⟩ : ∃ t, a = 2 * t ∨ a = 2 * t + 1 := ⟨a / 2, by omega⟩
      · obtain ⟨t, rfl | rfl⟩ : ∃ t, b = 2 * t ∨ b = 2 * t + 1 := ⟨b / 2, by omega⟩
        · subst hab
          have hn : 2 * r + 2 * t = 2 * (r + t) := by omega
          rw [hn, binDigitSum_two_mul, binDigitSum_two_mul, binDigitSum_two_mul]
          exact ih _ (by omega) _ _ rfl
        · subst hab
          have hn : 2 * r + (2 * t + 1) = 2 * (r + t) + 1 := by omega
          rw [hn, binDigitSum_two_mul_add_one, binDigitSum_two_mul,
            binDigitSum_two_mul_add_one]
          have h := ih (r + t) (by omega) r t rfl
          omega
      · obtain ⟨t, rfl | rfl⟩ : ∃ t, b = 2 * t ∨ b = 2 * t + 1 := ⟨b / 2, by omega⟩
        · subst hab
          have hn : (2 * r + 1) + 2 * t = 2 * (r + t) + 1 := by omega
          rw [hn, binDigitSum_two_mul_add_one, binDigitSum_two_mul_add_one,
            binDigitSum_two_mul]
          have h := ih (r + t) (by omega) r t rfl
          omega
        · subst hab
          have hn : (2 * r + 1) + (2 * t + 1) = 2 * (r + t + 1) := by omega
          rw [hn, binDigitSum_two_mul, binDigitSum_two_mul_add_one,
            binDigitSum_two_mul_add_one]
          have h := ih (r + t) (by omega) r t rfl
          have hs := binDigitSum_succ_le (r + t)
          omega

private theorem transfer_even (k j : ℕ) (hjk : j ≤ k) :
    (binDigitSum (2 * j) + binDigitSum (2 * k - 2 * j) = binDigitSum (2 * k)) ↔
    (binDigitSum j + binDigitSum (k - j) = binDigitSum k) := by
  have hsub : 2 * k - 2 * j = 2 * (k - j) := by omega
  rw [binDigitSum_two_mul, hsub, binDigitSum_two_mul, binDigitSum_two_mul]

private theorem transfer_odd_lo (k j : ℕ) (hjk : j ≤ k) :
    (binDigitSum (2 * j) + binDigitSum (2 * k + 1 - 2 * j) =
      binDigitSum (2 * k + 1)) ↔
    (binDigitSum j + binDigitSum (k - j) = binDigitSum k) := by
  have hsub : 2 * k + 1 - 2 * j = 2 * (k - j) + 1 := by omega
  rw [binDigitSum_two_mul, hsub, binDigitSum_two_mul_add_one,
    binDigitSum_two_mul_add_one]
  constructor <;> intro h <;> omega

private theorem transfer_odd_hi (k j : ℕ) (hjk : j ≤ k) :
    (binDigitSum (2 * j + 1) + binDigitSum (2 * k + 1 - (2 * j + 1)) =
      binDigitSum (2 * k + 1)) ↔
    (binDigitSum j + binDigitSum (k - j) = binDigitSum k) := by
  have hsub : 2 * k + 1 - (2 * j + 1) = 2 * (k - j) := by omega
  rw [binDigitSum_two_mul_add_one, hsub, binDigitSum_two_mul,
    binDigitSum_two_mul_add_one]
  constructor <;> intro h <;> omega

private theorem odd_not_mem_even (k m : ℕ) (hm : m ≤ 2 * k) (hodd : Odd m) :
    ¬ (binDigitSum m + binDigitSum (2 * k - m) = binDigitSum (2 * k)) := by
  obtain ⟨r, rfl⟩ := hodd
  have h1 : binDigitSum (2 * r + 1) = binDigitSum r + 1 :=
    binDigitSum_two_mul_add_one r
  have hsub : 2 * k - (2 * r + 1) = 2 * (k - r - 1) + 1 := by omega
  have h2 : binDigitSum (2 * k - (2 * r + 1)) = binDigitSum (k - r - 1) + 1 := by
    rw [hsub, binDigitSum_two_mul_add_one]
  have h3 : binDigitSum (2 * k) = binDigitSum k := binDigitSum_two_mul k
  have hsplit : r + ((k - r - 1) + 1) = k := by omega
  have hle := binDigitSum_add_le k r ((k - r - 1) + 1) hsplit
  have hs := binDigitSum_succ_le (k - r - 1)
  rw [h1, h2, h3]
  intro hcon
  omega

/--
**Digital binomial theorem over a commutative semiring.** Let $s(m)$ denote the binary digit sum
of a natural number $m$. For every natural number $n$ and all elements $x$, $y$ of a commutative
semiring, $(x + y)^{s(n)}$ equals the sum of $x^{s(m)} y^{s(n - m)}$ over all $m$ with
$0 \le m \le n$ and $s(m) + s(n - m) = s(n)$.
-/
theorem digital_binomial_theorem_general
    (n : ℕ) {R : Type*} [CommSemiring R] (x y : R) :
    (x + y) ^ binDigitSum n =
      ∑ m ∈ Finset.filter
        (fun m => binDigitSum m + binDigitSum (n - m) = binDigitSum n)
        (Finset.range (n + 1)),
        x ^ binDigitSum m * y ^ binDigitSum (n - m) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · rw [binDigitSum_zero, pow_zero]
      have hset : Finset.filter
          (fun m => binDigitSum m + binDigitSum (0 - m) = 0)
          (Finset.range (0 + 1)) = {0} := by decide
      rw [hset, Finset.sum_singleton]
      simp [binDigitSum_zero]
    · obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
      · -- even case: doubling reindexes the carry-free set for `k`
        have ihk := ih k (by omega)
        have hpow : (x + y) ^ binDigitSum (2 * k) = (x + y) ^ binDigitSum k := by
          rw [binDigitSum_two_mul]
        rw [hpow, ihk]
        apply Finset.sum_bij (fun j _ => 2 * j)
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
          obtain ⟨hjmem, hjcond⟩ := hj
          refine ⟨by omega, ?_⟩
          show binDigitSum (2 * j) + binDigitSum (2 * k - 2 * j) =
            binDigitSum (2 * k)
          exact (transfer_even k j (by omega)).mpr hjcond
        · intro a₁ _ a₂ _ h
          have h2 : 2 * a₁ = 2 * a₂ := h
          omega
        · intro m hm
          simp only [Finset.mem_filter, Finset.mem_range] at hm
          obtain ⟨hmem, hmcond⟩ := hm
          have heven : Even m := by
            by_contra hcon
            rw [Nat.not_even_iff_odd] at hcon
            exact odd_not_mem_even k m (by omega) hcon hmcond
          obtain ⟨j, rfl⟩ := even_iff_two_dvd.mp heven
          exact ⟨j, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (by omega),
              (transfer_even k j (by omega)).mp hmcond⟩, rfl⟩
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_range] at hj
          obtain ⟨hjmem, hjcond⟩ := hj
          have hsub : 2 * k - 2 * j = 2 * (k - j) := by omega
          change x ^ binDigitSum j * y ^ binDigitSum (k - j) =
            x ^ binDigitSum (2 * j) * y ^ binDigitSum (2 * k - 2 * j)
          rw [binDigitSum_two_mul, hsub, binDigitSum_two_mul]
      · -- odd case: split into even and odd `m`, each copy gives the sum for `k`
        have ihk := ih k (by omega)
        have hpow : (x + y) ^ binDigitSum (2 * k + 1) =
            (x + y) ^ binDigitSum k * (x + y) := by
          rw [binDigitSum_two_mul_add_one, pow_succ]
        rw [hpow]
        have hsplit : Finset.filter
              (fun m => binDigitSum m + binDigitSum (2 * k + 1 - m) =
                binDigitSum (2 * k + 1))
              (Finset.range (2 * k + 1 + 1)) =
              Finset.image (fun j => 2 * j)
                (Finset.filter
                  (fun m => binDigitSum m + binDigitSum (k - m) = binDigitSum k)
                  (Finset.range (k + 1))) ∪
              Finset.image (fun j => 2 * j + 1)
                (Finset.filter
                  (fun m => binDigitSum m + binDigitSum (k - m) = binDigitSum k)
                  (Finset.range (k + 1))) := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
            Finset.mem_image]
          constructor
          · rintro ⟨hmem, hmcond⟩
            obtain ⟨j, rfl | rfl⟩ : ∃ t, m = 2 * t ∨ m = 2 * t + 1 :=
              ⟨m / 2, by omega⟩
            · left
              exact ⟨j, ⟨by omega, (transfer_odd_lo k j (by omega)).mp hmcond⟩,
                rfl⟩
            · right
              exact ⟨j, ⟨by omega, (transfer_odd_hi k j (by omega)).mp hmcond⟩,
                rfl⟩
          · rintro (⟨j, ⟨hjmem, hjcond⟩, rfl⟩ | ⟨j, ⟨hjmem, hjcond⟩, rfl⟩)
            · exact ⟨by omega, (transfer_odd_lo k j (by omega)).mpr hjcond⟩
            · exact ⟨by omega, (transfer_odd_hi k j (by omega)).mpr hjcond⟩
        have hdisj : Disjoint
            (Finset.image (fun j => 2 * j)
              (Finset.filter
                (fun m => binDigitSum m + binDigitSum (k - m) = binDigitSum k)
                (Finset.range (k + 1))))
            (Finset.image (fun j => 2 * j + 1)
              (Finset.filter
                (fun m => binDigitSum m + binDigitSum (k - m) = binDigitSum k)
                (Finset.range (k + 1)))) := by
          rw [Finset.disjoint_left]
          intro m hm1 hm2
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hm1
          obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hm2
          have ht2 : 2 * t + 1 = 2 * j := ht
          omega
        have hinj1 : Set.InjOn (fun j => 2 * j)
            ↑(Finset.filter
              (fun m => binDigitSum m + binDigitSum (k - m) = binDigitSum k)
              (Finset.range (k + 1))) := by
          intro a _ b _ h
          have h2 : 2 * a = 2 * b := h
          omega
        have hinj2 : Set.InjOn (fun j => 2 * j + 1)
            ↑(Finset.filter
              (fun m => binDigitSum m + binDigitSum (k - m) = binDigitSum k)
              (Finset.range (k + 1))) := by
          intro a _ b _ h
          have h2 : 2 * a + 1 = 2 * b + 1 := h
          omega
        have hE : (∑ m ∈ Finset.image (fun j => 2 * j)
              (Finset.filter
                (fun m => binDigitSum m + binDigitSum (k - m) = binDigitSum k)
                (Finset.range (k + 1))),
              x ^ binDigitSum m * y ^ binDigitSum (2 * k + 1 - m)) =
            (∑ j ∈ Finset.filter
              (fun m => binDigitSum m + binDigitSum (k - m) = binDigitSum k)
              (Finset.range (k + 1)),
              x ^ binDigitSum j * y ^ binDigitSum (k - j)) * y := by
          rw [Finset.sum_image hinj1, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_range] at hj
          obtain ⟨hjmem, hjcond⟩ := hj
          have hsub : 2 * k + 1 - 2 * j = 2 * (k - j) + 1 := by omega
          change x ^ binDigitSum (2 * j) * y ^ binDigitSum (2 * k + 1 - 2 * j) =
            x ^ binDigitSum j * y ^ binDigitSum (k - j) * y
          rw [binDigitSum_two_mul, hsub, binDigitSum_two_mul_add_one, pow_succ]
          ring
        have hO : (∑ m ∈ Finset.image (fun j => 2 * j + 1)
              (Finset.filter
                (fun m => binDigitSum m + binDigitSum (k - m) = binDigitSum k)
                (Finset.range (k + 1))),
              x ^ binDigitSum m * y ^ binDigitSum (2 * k + 1 - m)) =
            x * (∑ j ∈ Finset.filter
              (fun m => binDigitSum m + binDigitSum (k - m) = binDigitSum k)
              (Finset.range (k + 1)),
              x ^ binDigitSum j * y ^ binDigitSum (k - j)) := by
          rw [Finset.sum_image hinj2, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_range] at hj
          obtain ⟨hjmem, hjcond⟩ := hj
          have hsub : 2 * k + 1 - (2 * j + 1) = 2 * (k - j) := by omega
          change x ^ binDigitSum (2 * j + 1) * y ^ binDigitSum (2 * k + 1 - (2 * j + 1)) =
            x * (x ^ binDigitSum j * y ^ binDigitSum (k - j))
          rw [binDigitSum_two_mul_add_one, hsub, binDigitSum_two_mul, pow_succ']
          ring
        rw [hsplit, Finset.sum_union hdisj, hE, hO, ihk]
        ring

/--
**Digital binomial theorem.** Let $s(m)$ denote the binary digit sum of a natural number $m$. For
every natural number $n$ and all elements $x$, $y$ of a commutative ring, $(x + y)^{s(n)}$ equals
the sum of $x^{s(m)} y^{s(n - m)}$ over all $m$ with $0 \le m \le n$ and
$s(m) + s(n - m) = s(n)$.

The condition $s(m) + s(n - m) = s(n)$ says that adding $m$ and $n - m$ in binary produces no
carries; equivalently, $m$ has a binary digit $1$ only in positions where $n$ has one.

Proves `Wanted` entry `digital_binomial_theorem`.

Source: Hieu D. Nguyen,
"A Generalization of the Digital Binomial Theorem,"
Journal of Integer Sequences 18 (2015), Article 15.5.7,
Theorem (label th:digital-binomial-theorem),
equation (label eq:digital-binomial-theorem-carry-free), lines 107–113,
https://cs.uwaterloo.ca/journals/JIS/VOL18/Nguyen/nguyen6.tex
-/
theorem digital_binomial_theorem
    (n : ℕ) {R : Type*} [CommRing R] (x y : R) :
    (x + y) ^ binDigitSum n =
      ∑ m ∈ Finset.filter
        (fun m => binDigitSum m + binDigitSum (n - m) = binDigitSum n)
        (Finset.range (n + 1)),
        x ^ binDigitSum m * y ^ binDigitSum (n - m) :=
  digital_binomial_theorem_general n x y

end MetaMathlibExt
