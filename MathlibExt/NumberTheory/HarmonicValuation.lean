/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Positivity

/-!
# The `2`-adic valuation of differences of harmonic numbers

Results from Tamás Lengyel, *On the 2-Adic Valuation of Differences of
Harmonic Numbers*, INTEGERS 24 (2024), Article A27, on `ν₂(H_n - H_m)`, where
`H_n = harmonic n`.

Everything rests on one formula, `padicValRat_two_harmonic_sub`: for `m ≤ n`,
`ν₂(H_n - H_m) = -max_{m < k ≤ n} ν₂(k)`, where the maximum is written
`(Finset.Ioc m n).sup (padicValNat 2)` and is `0` for `m = n`. As in
Mathlib's `padicValRat_two_harmonic`, it is proved by induction on `n`: for
`m < n` the maximum of `ν₂` over `(m, n]` is never `ν₂(n + 1)`
(`sup_Ioc_padicValNat_two_ne`), so at each step the valuation of the sum is
the minimum of the two valuations.

The maximum is then evaluated in two ways (for a prime `p`).

* `sup_Ioc_padicValNat_eq`: if `p ^ r * c` is the only multiple of `p ^ r` in
  `(m, n]`, then the maximum of `ν_p` over `(m, n]` is `r + ν_p(c)`. This
  gives Lemma 1, Corollary 1, Theorem 5 and both branches of Theorem 6.
* `le_sup_Ioc_padicValNat_iff`: for `m < n`, the maximum is at least `j`
  exactly when `⌊m / p^j⌋ < ⌊n / p^j⌋`. Two consecutive integers contain an
  even one, which gives Theorem 2. The maximum is `a` exactly when
  `p^(a+1) ⌊n / p^(a+1)⌋ ≤ m < p^a ⌊n / p^a⌋` (`sup_Ioc_padicValNat_eq_iff`),
  so for `p = 2` the number of `m < n` with maximum `a` is `2 ^ a` if bit `a`
  of `n` is set and `0` otherwise (`card_filter_sup_Ioc_padicValNat_two_eq`).
  This gives Theorem 3 and, summing over these fibers, Corollary 2.

Theorem 4, the recurrence for `weightedBinaryDigitSum`, is a computation with
binary digits (`Nat.testBit`).

## Main results

* `padicValRat_two_harmonic_sub`: `ν₂(H_n - H_m) = -max_{m < k ≤ n} ν₂(k)`.
* `padicValRat_two_harmonic_sub_neg` (Theorem 2, Kürschák).
* `card_filter_padicValRat_two_harmonic_sub` (Theorem 3).
* `padicValRat_two_harmonic_two_mul_sub` (Lemma 1),
  `padicValRat_two_harmonic_pow_sub` (Corollary 1).
* `sum_padicValRat_two_harmonic_sub` (Corollary 2),
  `weightedBinaryDigitSum_recurrence` (Theorem 4).
* `padicValRat_two_harmonic_sub_pow` (Theorem 5),
  `padicValRat_two_harmonic_sub_piecewise` (Theorem 6, formula (3.1)).

## References

* Tamás Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
  Numbers*, INTEGERS 24 (2024), Article A27.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The weighted binary digit sum `a(n) = ∑ aᵢ * 2^{aᵢ}`, summed over the
exponents `aᵢ` of the powers of `2` in the binary expansion of `n` (that is,
over the indices of the `1` bits of `n`).

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Corollary 2 and Theorem 4; the
first values `0, 0, 2, 2, 8, 8, 10, 10, 24, ...` are displayed there. -/
def weightedBinaryDigitSum (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (Nat.log 2 n + 1), if Nat.testBit n i then i * 2 ^ i else 0

/-- Characteristic value `a(2) = 2`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Theorem 4 (displayed values). -/
theorem weightedBinaryDigitSum_two : weightedBinaryDigitSum 2 = 2 := by
  decide

/-- Characteristic value `a(4) = 8`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Theorem 4 (displayed values). -/
theorem weightedBinaryDigitSum_four : weightedBinaryDigitSum 4 = 8 := by
  decide

/-! ### Binary digits -/

/-- A natural number `n < 2 ^ K` is the sum of the powers `2 ^ i`, `i < K`,
over its `1` bits. -/
theorem sum_range_testBit_two_pow {n K : ℕ} (h : n < 2 ^ K) :
    ∑ i ∈ Finset.range K, (if n.testBit i then 2 ^ i else 0) = n := by
  induction K generalizing n with
  | zero => simp_all
  | succ K ih =>
    have key : ∑ i ∈ Finset.range K,
        (if n.testBit (i + 1) then 2 ^ (i + 1) else 0) =
        2 * ∑ i ∈ Finset.range K, (if (n / 2).testBit i then 2 ^ i else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.testBit_add_one]
      split_ifs <;> ring
    rw [Finset.sum_range_succ', key, ih (by rw [pow_succ] at h; omega),
      Nat.testBit_zero]
    split_ifs with h0 <;> simp only [decide_eq_true_eq] at h0 <;> omega

/-- The sum defining `weightedBinaryDigitSum n` may be taken over the indices
below any `K` with `n < 2 ^ K`. -/
theorem weightedBinaryDigitSum_eq_sum_range {n K : ℕ} (h : n < 2 ^ K) :
    weightedBinaryDigitSum n =
      ∑ i ∈ Finset.range K, if n.testBit i then i * 2 ^ i else 0 := by
  have hext : ∀ {K K' : ℕ}, n < 2 ^ K → K ≤ K' →
      ∑ i ∈ Finset.range K', (if n.testBit i then i * 2 ^ i else 0) =
        ∑ i ∈ Finset.range K, (if n.testBit i then i * 2 ^ i else 0) := by
    intro K K' h hK
    refine (Finset.sum_subset (Finset.range_subset_range.2 hK)
      fun i _ hi => ?_).symm
    rw [Finset.mem_range, not_lt] at hi
    rw [Nat.testBit_eq_false_of_lt
      (h.trans_le (Nat.pow_le_pow_right two_pos hi))]
    rfl
  rw [weightedBinaryDigitSum,
    ← hext (Nat.lt_pow_succ_log_self one_lt_two n) (le_max_right K _),
    hext h (le_max_left K _)]

/-! ### The largest `p`-adic valuation in an interval -/

/-- The interval `(m, n]` contains a multiple of `d > 0` exactly when
`m / d < n / d`. -/
theorem exists_mem_Ioc_dvd_iff {d m n : ℕ} (hd : 0 < d) :
    (∃ k ∈ Finset.Ioc m n, d ∣ k) ↔ m / d < n / d := by
  constructor
  · rintro ⟨k, hk, c, rfl⟩
    rw [Finset.mem_Ioc] at hk
    have h1 : m / d < c :=
      (Nat.div_lt_iff_lt_mul hd).2 (by rw [mul_comm]; exact hk.1)
    have h2 : c ≤ n / d :=
      (Nat.le_div_iff_mul_le hd).2 (by rw [mul_comm]; exact hk.2)
    omega
  · intro h
    refine ⟨d * (n / d), Finset.mem_Ioc.2 ⟨?_, Nat.mul_div_le n d⟩,
      dvd_mul_right _ _⟩
    calc m < d * (m / d + 1) := Nat.lt_mul_div_succ m hd
      _ ≤ d * (n / d) := Nat.mul_le_mul_left _ h

/-- For a prime `p` and `m < n`, the largest `p`-adic valuation of an element
of `(m, n]` is at least `j` exactly when `m / p ^ j < n / p ^ j`, that is,
when `(m, n]` contains a multiple of `p ^ j`. -/
theorem le_sup_Ioc_padicValNat_iff {p m n j : ℕ} (hp : p.Prime) (h : m < n) :
    j ≤ (Finset.Ioc m n).sup (padicValNat p) ↔ m / p ^ j < n / p ^ j := by
  have := Fact.mk hp
  rw [← exists_mem_Ioc_dvd_iff (pow_pos hp.pos j)]
  constructor
  · intro hj
    obtain ⟨k, hk, hsup⟩ :=
      Finset.exists_mem_eq_sup _ (Finset.nonempty_Ioc.2 h) (padicValNat p)
    have hk0 : k ≠ 0 := by have := (Finset.mem_Ioc.1 hk).1; omega
    exact ⟨k, hk, (padicValNat_dvd_iff_le hk0).2 (hsup ▸ hj)⟩
  · rintro ⟨k, hk, hdvd⟩
    have hk0 : k ≠ 0 := by have := (Finset.mem_Ioc.1 hk).1; omega
    exact ((padicValNat_dvd_iff_le hk0).1 hdvd).trans (Finset.le_sup hk)

/-- For a prime `p` and `m < n`, the largest `p`-adic valuation of an element
of `(m, n]` is `a` exactly when `p ^ (a + 1) * ⌊n / p ^ (a + 1)⌋ ≤ m` and
`m < p ^ a * ⌊n / p ^ a⌋`. -/
theorem sup_Ioc_padicValNat_eq_iff {p m n a : ℕ} (hp : p.Prime) (h : m < n) :
    (Finset.Ioc m n).sup (padicValNat p) = a ↔
      p ^ (a + 1) * (n / p ^ (a + 1)) ≤ m ∧ m < p ^ a * (n / p ^ a) := by
  rw [le_antisymm_iff, ← not_lt, Nat.lt_iff_add_one_le,
    le_sup_Ioc_padicValNat_iff hp h, le_sup_Ioc_padicValNat_iff hp h, not_lt,
    Nat.le_div_iff_mul_le (pow_pos hp.pos _),
    Nat.div_lt_iff_lt_mul (pow_pos hp.pos _), mul_comm, mul_comm (n / p ^ a)]

/-- If `p ^ r * c` is the only multiple of `p ^ r` in `(m, n]` (that is,
`p ^ r * (c - 1) ≤ m < p ^ r * c ≤ n < p ^ r * (c + 1)`), then the largest
`p`-adic valuation of an element of `(m, n]` is `r + ν_p(c)`. -/
theorem sup_Ioc_padicValNat_eq {p m n r c : ℕ} (hp : p.Prime)
    (hlo : p ^ r * c ≤ m + p ^ r) (hm : m < p ^ r * c) (hn : p ^ r * c ≤ n)
    (hhi : n < p ^ r * c + p ^ r) :
    (Finset.Ioc m n).sup (padicValNat p) = r + padicValNat p c := by
  have := Fact.mk hp
  have hpr : 0 < p ^ r := pow_pos hp.pos r
  have hc : c ≠ 0 := by rintro rfl; simp at hm
  have hval : padicValNat p (p ^ r * c) = r + padicValNat p c := by
    rw [padicValNat.mul hpr.ne' hc, padicValNat.prime_pow]
  refine le_antisymm (Finset.sup_le fun k hk => ?_)
    (hval ▸ Finset.le_sup (Finset.mem_Ioc.2 ⟨hm, hn⟩))
  rw [Finset.mem_Ioc] at hk
  by_cases hkr : padicValNat p k < r
  · omega
  · obtain ⟨c', rfl⟩ := (padicValNat_dvd_iff_le (by omega)).2 (not_lt.1 hkr)
    have h1 : c < c' + 1 := by
      rw [← Nat.mul_lt_mul_left hpr, mul_add, mul_one]; omega
    have h2 : c' < c + 1 := by
      rw [← Nat.mul_lt_mul_left hpr, mul_add, mul_one]; omega
    rw [show c' = c by omega, hval]

/-- For `m < n`, the largest `2`-adic valuation of an element of `(m, n]` is
not `ν₂(n + 1)`: otherwise `(m, n + 1]` would contain two odd multiples of
`2 ^ ν₂(n + 1)` and hence a multiple of `2 ^ (ν₂(n + 1) + 1)` in `(m, n]`. -/
theorem sup_Ioc_padicValNat_two_ne {m n : ℕ} (h : m < n) :
    (Finset.Ioc m n).sup (padicValNat 2) ≠ padicValNat 2 (n + 1) := by
  intro heq
  set j := padicValNat 2 (n + 1)
  have h1 := (le_sup_Ioc_padicValNat_iff Nat.prime_two h (j := j)).1 heq.ge
  have h2 := mt (le_sup_Ioc_padicValNat_iff Nat.prime_two h (j := j + 1)).2
    (by omega)
  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at h2
  have hd : 2 ^ j ∣ n + 1 := pow_padicValNat_dvd
  have hnd : ¬ 2 ^ (j + 1) ∣ n + 1 :=
    pow_succ_padicValNat_not_dvd n.succ_ne_zero
  have hq := Nat.succ_div_of_dvd hd
  obtain ⟨t, ht⟩ := hd
  have ht' : (n + 1) / 2 ^ j = t := by
    rw [ht, Nat.mul_div_cancel_left _ (by positivity)]
  have hodd : t % 2 = 1 := by
    by_contra hc
    apply hnd
    rw [ht, pow_succ]
    exact Nat.mul_dvd_mul_left _ (Nat.dvd_of_mod_eq_zero (by omega))
  omega

/-- The number of `m < n` for which the largest `2`-adic valuation of an
element of `(m, n]` is `a` equals `2 ^ a` times bit `a` of `n`. -/
theorem card_filter_sup_Ioc_padicValNat_two_eq (n a : ℕ) :
    ((Finset.range n).filter
      (fun m => (Finset.Ioc m n).sup (padicValNat 2) = a)).card =
      2 ^ a * (n / 2 ^ a % 2) := by
  have hfilter : (Finset.range n).filter
      (fun m => (Finset.Ioc m n).sup (padicValNat 2) = a) =
      Finset.Ico (2 ^ (a + 1) * (n / 2 ^ (a + 1))) (2 ^ a * (n / 2 ^ a)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hmn, hsup⟩
      exact (sup_Ioc_padicValNat_eq_iff Nat.prime_two hmn).1 hsup
    · intro hm
      have hmn : m < n := hm.2.trans_le (Nat.mul_div_le n _)
      exact ⟨hmn, (sup_Ioc_padicValNat_eq_iff Nat.prime_two hmn).2 hm⟩
  rw [hfilter, Nat.card_Ico, pow_succ, ← Nat.div_div_eq_div_mul, mul_assoc,
    ← Nat.mul_sub]
  congr 1
  omega

/-- Summing the largest `2`-adic valuation of an element of `(m, n]` over
`m < n` gives the weighted binary digit sum of `n`. -/
theorem sum_range_sup_Ioc_padicValNat_two (n : ℕ) :
    ∑ m ∈ Finset.range n, (Finset.Ioc m n).sup (padicValNat 2) =
      weightedBinaryDigitSum n := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := Finset.range (Nat.log 2 n + 1))
    (g := fun m => (Finset.Ioc m n).sup (padicValNat 2)),
    weightedBinaryDigitSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun m hm => (Finset.mem_filter.1 hm).2,
      Finset.sum_const, smul_eq_mul, card_filter_sup_Ioc_padicValNat_two_eq,
      Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with h | h <;>
      simp [h, mul_comm]
  · intro m _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.sup_le fun k hk => (padicValNat_le_nat_log k).trans
      (Nat.log_mono_right (Finset.mem_Ioc.1 hk).2)

/-! ### The `2`-adic valuation of `H_n - H_m` -/

/-- The harmonic numbers are strictly increasing. -/
theorem harmonic_strictMono : StrictMono harmonic :=
  strictMono_nat_of_lt_succ fun n => by
    rw [harmonic_succ]
    exact lt_add_of_pos_right _ (by positivity)

/-- For `m ≤ n`, the `2`-adic valuation of `H_n - H_m` is minus the largest
`2`-adic valuation of an element of `(m, n]`. -/
theorem padicValRat_two_harmonic_sub (m n : ℕ) (h : m ≤ n) :
    padicValRat 2 (harmonic n - harmonic m) =
      -(((Finset.Ioc m n).sup (padicValNat 2) : ℕ) : ℤ) := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [harmonic_succ, add_sub_right_comm,
      ← Finset.insert_Ioc_right_eq_Ioc_add_one hmn, Finset.sup_insert]
    rcases hmn.eq_or_lt with rfl | hlt
    · rw [sub_self, zero_add, padicValRat.inv, padicValRat.of_nat,
        Finset.Ioc_self, Finset.sup_empty]
      simp
    have hx : 0 < harmonic n - harmonic m :=
      sub_pos.2 (harmonic_strictMono hlt)
    have hy : (0 : ℚ) < ((n + 1 : ℕ) : ℚ)⁻¹ := by positivity
    have hne : padicValRat 2 (harmonic n - harmonic m) ≠
        padicValRat 2 ((n + 1 : ℕ) : ℚ)⁻¹ := by
      rw [ih, padicValRat.inv, padicValRat.of_nat, Ne, neg_inj, Nat.cast_inj]
      exact sup_Ioc_padicValNat_two_ne hlt
    rw [padicValRat.add_eq_min (by positivity) hx.ne' hy.ne' hne, ih,
      padicValRat.inv, padicValRat.of_nat, min_neg_neg, ← Nat.cast_max,
      max_comm]

/-! ### Lengyel's results -/

/-- Kürschák's strengthening of Theisinger's theorem: for `0 ≤ m ≤ n - 2`
the difference `H_n - H_m` does not lie in the ring of `2`-adic integers.

For a rational number this is the statement that its `2`-adic valuation
`padicValRat 2` is negative; in particular `H_n - H_m ∉ ℤ`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Theorem 2
(`integers-2024-A27-thm-2`).

Proves `Wanted` entry `padicValRat_two_harmonic_sub_neg`. -/
theorem padicValRat_two_harmonic_sub_neg (m n : ℕ)
    (h : m + 2 ≤ n) :
    padicValRat 2 (harmonic n - harmonic m) < 0 := by
  rw [padicValRat_two_harmonic_sub m n (by omega), neg_lt_zero, Nat.cast_pos,
    ← Nat.one_le_iff_ne_zero.trans Nat.pos_iff_ne_zero.symm,
    le_sup_Ioc_padicValNat_iff Nat.prime_two (by omega), pow_one]
  omega

/-- Fiber counts of the values `ν₂(H_n - H_m)`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Theorem 3
(`integers-2024-A27-thm-3`): writing `n = ∑_{i=1}^{t} 2^{aᵢ}` in binary,
among the values `ν₂(H_n - H_m)` for `m = 0, 1, …, n - 1` exactly `2^{aᵢ}`
are equal to `-aᵢ`, for each exponent `aᵢ` occurring in the expansion.

The extracted statement truncates the refinement locating these values in
the intervals determined by the partial sums `Mⱼ`; only the fiber counts
stated in the first part are formalized here. Verified computationally with
exact rational arithmetic for `n < 40`.

Proves `Wanted` entry `card_filter_padicValRat_two_harmonic_sub`. -/
theorem card_filter_padicValRat_two_harmonic_sub (n a : ℕ)
    (ha : Nat.testBit n a = true) :
    ((Finset.range n).filter
      (fun m => padicValRat 2 (harmonic n - harmonic m) = -(a : ℤ))).card
      = 2 ^ a := by
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at ha
  rw [Finset.filter_congr fun m hm => by
      rw [padicValRat_two_harmonic_sub m n (Finset.mem_range.1 hm).le,
        neg_inj, Nat.cast_inj],
    card_filter_sup_Ioc_padicValNat_two_eq, ha, mul_one]

/-- Valuation of the difference `H_{2n} - H_n`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Lemma 1
(`integers-2024-A27-lem-1`): for `n ≥ 1`,
`ν₂(H_{2n} - H_n) = -⌊log₂(2n)⌋`.

Proves `Wanted` entry `padicValRat_two_harmonic_two_mul_sub`. -/
theorem padicValRat_two_harmonic_two_mul_sub (n : ℕ)
    (hn : 1 ≤ n) :
    padicValRat 2 (harmonic (2 * n) - harmonic n) =
      -(Nat.log 2 (2 * n) : ℤ) := by
  have h1 := Nat.pow_log_le_self 2 (show 2 * n ≠ 0 by omega)
  have h2 := Nat.lt_pow_succ_log_self one_lt_two (2 * n)
  rw [Nat.succ_eq_add_one, pow_succ] at h2
  rw [padicValRat_two_harmonic_sub n (2 * n) (by omega),
    sup_Ioc_padicValNat_eq (r := Nat.log 2 (2 * n)) (c := 1) Nat.prime_two
      (by omega) (by omega) (by omega) (by omega), padicValNat_one_right,
    add_zero]

/-- Valuation at powers of two.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Corollary 1
(`integers-2024-A27-cor-1`): if `n = 2^a` is a power of `2` then
`ν₂(H_n - H_{n-m}) = -a` for every `1 ≤ m ≤ n`.

Proves `Wanted` entry `padicValRat_two_harmonic_pow_sub`. -/
theorem padicValRat_two_harmonic_pow_sub (a m : ℕ)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ a) :
    padicValRat 2 (harmonic (2 ^ a) - harmonic (2 ^ a - m)) = -(a : ℤ) := by
  rw [padicValRat_two_harmonic_sub _ _ (Nat.sub_le _ _),
    sup_Ioc_padicValNat_eq (r := a) (c := 1) Nat.prime_two
      (by omega) (by omega) (by omega) (by omega), padicValNat_one_right,
    add_zero]

/-- Sum of valuations over all `m < n`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Corollary 2
(`integers-2024-A27-cor-2`): `∑_{m=0}^{n-1} ν₂(H_n - H_m) = -a(n)`, where
`a(n) = weightedBinaryDigitSum n`.

The extracted statement flattens the displayed aggregation over `m`; the sum
reading used here (rather than a product of valuations) was verified
computationally with exact rational arithmetic for `n ≤ 16`.

Proves `Wanted` entry `sum_padicValRat_two_harmonic_sub`. -/
theorem sum_padicValRat_two_harmonic_sub (n : ℕ) :
    ∑ m ∈ Finset.range n, padicValRat 2 (harmonic n - harmonic m)
      = -(weightedBinaryDigitSum n : ℤ) := by
  rw [Finset.sum_congr rfl fun m hm =>
      padicValRat_two_harmonic_sub m n (Finset.mem_range.1 hm).le,
    Finset.sum_neg_distrib, ← Nat.cast_sum, sum_range_sup_Ioc_padicValNat_two]

/-- Recurrence for the weighted binary digit sum.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Theorem 4
(`integers-2024-A27-thm-4`): the weighted binary digit sum satisfies
`a(2n) = 2a(n) + 2n` and `a(2n + 1) = a(2n)`, with `a(0) = a(1) = 0`.

The two-variable generating-function claim in the same theorem is garbled in
the extraction and is not formalized.

Proves `Wanted` entry `weightedBinaryDigitSum_recurrence`. -/
theorem weightedBinaryDigitSum_recurrence (n : ℕ) :
    weightedBinaryDigitSum (2 * n) = 2 * weightedBinaryDigitSum n + 2 * n ∧
    weightedBinaryDigitSum (2 * n + 1) = weightedBinaryDigitSum (2 * n) := by
  have hn : n < 2 ^ n := Nat.lt_two_pow_self
  have h2n : 2 * n < 2 ^ (n + 1) := by rw [pow_succ]; omega
  have h2n1 : 2 * n + 1 < 2 ^ (n + 1) := by rw [pow_succ]; omega
  -- The bits of `2 * n` and `2 * n + 1` above bit `0` are the bits of `n`.
  have hshift : ∀ x, x / 2 = n →
      ∑ i ∈ Finset.range (n + 1), (if x.testBit i then i * 2 ^ i else 0) =
        ∑ i ∈ Finset.range n,
          (if n.testBit i then (i + 1) * 2 ^ (i + 1) else 0) := by
    intro x hx
    rw [Finset.sum_range_succ']
    simp only [Nat.testBit_add_one, hx, zero_mul, ite_self, add_zero]
  rw [weightedBinaryDigitSum_eq_sum_range h2n,
    weightedBinaryDigitSum_eq_sum_range h2n1,
    weightedBinaryDigitSum_eq_sum_range hn, hshift _ (by omega),
    hshift _ (by omega)]
  refine ⟨?_, rfl⟩
  calc
    _ = 2 * (∑ i ∈ Finset.range n, if n.testBit i then i * 2 ^ i else 0) +
        2 * (∑ i ∈ Finset.range n, if n.testBit i then 2 ^ i else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    _ = _ := by rw [sum_range_testBit_two_pow hn]

/-- Valuation for shifts by powers of two.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Theorem 5
(`integers-2024-A27-thm-5`): for `m = 2^r` with `1 ≤ m ≤ n`,
`ν₂(H_n - H_{n-m}) = -r - ν₂(⌊n / m⌋)`.

Proves `Wanted` entry `padicValRat_two_harmonic_sub_pow`. -/
theorem padicValRat_two_harmonic_sub_pow (r n : ℕ)
    (h : 2 ^ r ≤ n) :
    padicValRat 2 (harmonic n - harmonic (n - 2 ^ r))
      = -(r : ℤ) - ((n / 2 ^ r).factorization 2 : ℤ) := by
  have h1 := Nat.mul_div_le n (2 ^ r)
  have h2 := Nat.lt_mul_div_succ n (pow_pos two_pos r)
  rw [mul_add, mul_one] at h2
  rw [padicValRat_two_harmonic_sub _ _ (Nat.sub_le _ _),
    sup_Ioc_padicValNat_eq (r := r) (c := n / 2 ^ r) Nat.prime_two
      (by omega) (by omega) h1 (by omega),
    Nat.factorization_def _ Nat.prime_two]
  push_cast
  ring

/-- Piecewise valuation formula.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Theorem 6, formula (3.1)
(`integers-2024-A27-thm-6`): let `M = ⌈log₂(m + 1)⌉` and
`j = ⌊(n - m) / 2^M⌋`, where `1 ≤ m ≤ n`. Then `ν₂(H_n - H_{n-m}) = -M + 1`
when `2^M * j + m ≤ n ≤ 2^M * (j + 1) - 1`, and
`ν₂(H_n - H_{n-m}) = -M - ν₂(j + 1)` when
`2^M * (j + 1) ≤ n ≤ 2^M * (j + 1) + m - 1`.

The accompanying lower bound (3.2) is garbled in the extraction and is not
formalized. Both branches were verified computationally with exact rational
arithmetic for `m < 20`, `n < 45`.

Proves `Wanted` entry `padicValRat_two_harmonic_sub_piecewise`. -/
theorem padicValRat_two_harmonic_sub_piecewise (m n : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    (2 ^ (Nat.clog 2 (m + 1)) * ((n - m) / 2 ^ (Nat.clog 2 (m + 1))) + m ≤ n ∧
        n + 1 ≤
          2 ^ (Nat.clog 2 (m + 1)) * ((n - m) / 2 ^ (Nat.clog 2 (m + 1)) + 1) →
      padicValRat 2 (harmonic n - harmonic (n - m))
        = -(Nat.clog 2 (m + 1) : ℤ) + 1) ∧
    (2 ^ (Nat.clog 2 (m + 1)) * ((n - m) / 2 ^ (Nat.clog 2 (m + 1)) + 1) ≤
          n ∧
        n + 1 ≤
          2 ^ (Nat.clog 2 (m + 1)) *
            ((n - m) / 2 ^ (Nat.clog 2 (m + 1)) + 1) + m →
      padicValRat 2 (harmonic n - harmonic (n - m))
        = -(Nat.clog 2 (m + 1) : ℤ)
          - (((n - m) / 2 ^ (Nat.clog 2 (m + 1)) + 1).factorization 2 : ℤ))
    := by
  have hM1 := Nat.le_pow_clog one_lt_two (m + 1)
  have hM0 := Nat.clog_pos one_lt_two (show 1 < m + 1 by omega)
  have hM2 := Nat.pow_pred_clog_lt_self one_lt_two (show 1 < m + 1 by omega)
  generalize Nat.clog 2 (m + 1) = M at hM1 hM0 hM2 ⊢
  have hj := Nat.mul_div_le (n - m) (2 ^ M)
  generalize (n - m) / 2 ^ M = j at hj ⊢
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [Nat.pred_succ] at hM2
  -- With `E = 2 ^ M'`, the window `(n - m, n]` has length `m ∈ [E, 2E)`.
  have hE : 2 ^ (M' + 1) = 2 ^ M' * 2 := pow_succ 2 M'
  have e1 : 2 ^ M' * (2 * j + 1) = 2 ^ (M' + 1) * j + 2 ^ M' := by
    rw [hE]; ring
  have e2 : 2 ^ (M' + 1) * (j + 1) = 2 ^ (M' + 1) * j + 2 ^ (M' + 1) := by
    ring
  rw [padicValRat_two_harmonic_sub _ _ (Nat.sub_le _ _)]
  constructor
  · -- The only multiple of `2 ^ M'` in the window is `2 ^ M' * (2 * j + 1)`.
    rintro ⟨h1, h2⟩
    rw [e2] at h2
    rw [sup_Ioc_padicValNat_eq (r := M') (c := 2 * j + 1) Nat.prime_two
      (by omega) (by omega) (by omega) (by omega),
      padicValNat.eq_zero_of_not_dvd (by omega)]
    push_cast
    ring
  · -- The only multiple of `2 ^ (M' + 1)` in the window is
    -- `2 ^ (M' + 1) * (j + 1)`.
    rintro ⟨h1, h2⟩
    rw [e2] at h1 h2
    rw [sup_Ioc_padicValNat_eq (r := M' + 1) (c := j + 1) Nat.prime_two
      (by omega) (by omega) (by omega) (by omega),
      Nat.factorization_def _ Nat.prime_two]
    push_cast
    ring

end

end MetaMathlibExt
