/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Lucas numbers modulo m

The residues `{L_n mod m}` form a complete residue system iff
`m ∈ {2, 4, 6, 7, 14}` or `m = 3^k`.

The main result, `Statement_holds`, proves this theorem of Avila and Chen (its docstring cites
their paper). The proof below is a self-contained elementary argument.

## Proof outline

Write `L_n` for `MetaMathlibExt.lucasNumber n` and `F_n` for `Nat.fib n`.

* If the Lucas numbers attain every residue modulo `m`, they attain every residue modulo each
  divisor of `m`.
* Let `p ∉ {2, 3, 7}` be a prime. If `5` is a square modulo `p`, then `x ^ 2 = x + 1` has the two
  nonzero roots `(1 ± √5) / 2` in `ZMod p`, so `L_n = α ^ n + β ^ n` has period dividing `p - 1`
  and takes at most `p - 1` values. Otherwise the invariant
  `L_{n+1} ^ 2 - L_{n+1} L_n - L_n ^ 2 = 5 (-1) ^ (n + 1)` gives
  `(2 L_{n+1} - L_n) ^ 2 = 5 (L_n ^ 2 ± 4)`, so `L_n` misses every residue `t` for which
  `t ^ 2 - 4` and `t ^ 2 + 4` are nonzero squares; such a `t` is written down explicitly, according
  to which of `-1`, `2` and `3` are squares modulo `p`.
* Periodicity computations show that every residue is attained modulo `2, 4, 6, 7, 14`, and that
  some residue is missed modulo `8, 12, 18, 21, 28, 49`.
* For powers of `3`: `F_{8·3^k} ≡ 3^(k+1)` and `F_{8·3^k - 1} ≡ 1 + 3^(k+1)` modulo `3^(k+2)`,
  hence `L_{n + 8·3^k} ≡ L_n + 3^(k+1) L_{n+2} [ZMOD 3^(k+2)]`. As `3 ∤ L_{n+2}` is preserved by
  these shifts, a residue modulo `3^(k+1)` attained at such an index lifts to all three residues
  above it modulo `3^(k+2)`.
* A modulus all of whose prime factors lie in `{2, 3, 7}` and that is divisible by none of
  `8, 12, 18, 21, 28, 49` is one of `2, 4, 6, 7, 14` or a power of `3`.
-/

namespace MathlibExt.NumberTheory.LucasNumbersModuloMWanted

/-- **Classification of moduli for which the Lucas numbers attain every residue.** The
proposition that for every integer $m > 1$, with $L_n$ the Lucas numbers, every residue modulo
$m$ is attained (for every $r$ with $0 \le r < m$ there is $n \ge 0$ with
$L_n \equiv r \pmod m$) if and only if $m \in \{2, 4, 6, 7, 14\}$ or $m = 3^k$ for some
integer $k \ge 1$.

Source: OPG-37402, Lucas Numbers Modulo m [OpenGarden]. -/
def Statement : Prop :=
  ∀ (m : ℕ), 1 < m →
    ((∀ r : ℕ, r < m → ∃ n : ℕ, MetaMathlibExt.lucasNumber n % m = r) ↔
      (m = 2 ∨ m = 4 ∨ m = 6 ∨ m = 7 ∨ m = 14 ∨
        ∃ k : ℕ, 1 ≤ k ∧ m = 3 ^ k))

open MetaMathlibExt

/-! ### Basic facts -/

/-- The Lucas numbers attain every residue modulo `m`. -/
private def IsComplete (m : ℕ) : Prop :=
  ∀ r : ℕ, r < m → ∃ n : ℕ, lucasNumber n % m = r

private theorem lucasNumber_add_two (n : ℕ) :
    lucasNumber (n + 2) = lucasNumber (n + 1) + lucasNumber n := rfl

/-- The invariant `L_{n+1} ^ 2 - L_{n+1} L_n - L_n ^ 2 = 5 (-1) ^ (n + 1)`. -/
private theorem lucasNumber_succ_sq_sub (n : ℕ) :
    (lucasNumber (n + 1) : ℤ) ^ 2 - lucasNumber (n + 1) * lucasNumber n -
        (lucasNumber n : ℤ) ^ 2 = 5 * (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num [lucasNumber]
  | succ n ih =>
    rw [lucasNumber_add_two, Nat.cast_add]
    linear_combination (-1 : ℤ) * ih

/-- Attaining every residue modulo `m` passes to the divisors of `m`. -/
private theorem isComplete_of_dvd {m d : ℕ} (hc : IsComplete m) (hd : d ∣ m) (hm : 0 < m) :
    IsComplete d := by
  intro r hr
  obtain ⟨n, hn⟩ := hc r (lt_of_lt_of_le hr (Nat.le_of_dvd hm hd))
  exact ⟨n, by rw [← Nat.mod_mod_of_dvd _ hd, hn, Nat.mod_eq_of_lt hr]⟩

/-- If the Lucas numbers modulo `m` have a period `P < m`, they miss some residue modulo `m`. -/
private theorem not_isComplete_of_period {m P : ℕ} (hP0 : 0 < P) (hPm : P < m)
    (hper : ∀ n, lucasNumber (n + P) % m = lucasNumber n % m) : ¬IsComplete m := by
  intro hc
  have hmul : ∀ j k, lucasNumber (k + P * j) % m = lucasNumber k % m := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => intro k; rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]
  have hsub : Finset.range m ⊆ (Finset.range P).image (fun n => lucasNumber n % m) := by
    intro r hr
    obtain ⟨n, hn⟩ := hc r (Finset.mem_range.mp hr)
    refine Finset.mem_image.mpr ⟨n % P, Finset.mem_range.mpr (Nat.mod_lt _ hP0), ?_⟩
    rw [← hn, ← hmul (n / P) (n % P), Nat.mod_add_div]
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_range, Finset.card_range] at h1
  omega

/-! ### Computations modulo fixed moduli -/

/-- One step of the Lucas recurrence on pairs of residues modulo `m`. -/
private def lucasStep (m : ℕ) (x : ℕ × ℕ) : ℕ × ℕ := (x.2, (x.1 + x.2) % m)

/-- The pair `(L_n mod m, L_{n+1} mod m)`, computed by iterating `lucasStep`. -/
private def lucasPair (m n : ℕ) : ℕ × ℕ := (lucasStep m)^[n] (2 % m, 1 % m)

private theorem lucasPair_eq (m n : ℕ) :
    lucasPair m n = (lucasNumber n % m, lucasNumber (n + 1) % m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [lucasPair, Function.iterate_succ_apply', ← lucasPair, ih, lucasStep,
      lucasNumber_add_two, Nat.add_mod (lucasNumber (n + 1)), Nat.add_comm (lucasNumber n % m)]

private theorem lucasNumber_mod_eq_of_period {m P : ℕ} (hP : lucasPair m P = lucasPair m 0)
    (n : ℕ) : lucasNumber n % m = (lucasPair m (n % P)).1 := by
  have hadd : ∀ k, lucasPair m (k + P) = lucasPair m k := by
    intro k
    simp only [lucasPair] at hP ⊢
    rw [Function.iterate_add_apply, hP]
    rfl
  have hmul : ∀ j k, lucasPair m (k + P * j) = lucasPair m k := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => intro k; rw [Nat.mul_succ, ← Nat.add_assoc, hadd, ih]
  have h := hmul (n / P) (n % P)
  rw [Nat.mod_add_div] at h
  rw [← h, lucasPair_eq]

private theorem not_isComplete_of_lucasPair {m P r : ℕ} (hrm : r < m) (hP0 : 0 < P)
    (hP : lucasPair m P = lucasPair m 0) (hr : ∀ n < P, (lucasPair m n).1 ≠ r) :
    ¬IsComplete m := by
  intro hc
  obtain ⟨n, hn⟩ := hc r hrm
  rw [lucasNumber_mod_eq_of_period hP] at hn
  exact hr _ (Nat.mod_lt _ hP0) hn

private theorem isComplete_of_lucasPair {m P : ℕ} (h : ∀ r < m, ∃ n < P, (lucasPair m n).1 = r) :
    IsComplete m := by
  intro r hr
  obtain ⟨n, -, hn⟩ := h r hr
  rw [lucasPair_eq] at hn
  exact ⟨n, hn⟩

private theorem isComplete_two : IsComplete 2 := isComplete_of_lucasPair (P := 3) (by decide)

private theorem isComplete_four : IsComplete 4 := isComplete_of_lucasPair (P := 6) (by decide)

private theorem isComplete_six : IsComplete 6 := isComplete_of_lucasPair (P := 24) (by decide)

private theorem isComplete_seven : IsComplete 7 := isComplete_of_lucasPair (P := 16) (by decide)

private theorem isComplete_fourteen : IsComplete 14 :=
  isComplete_of_lucasPair (P := 48) (by decide)

private theorem not_isComplete_eight : ¬IsComplete 8 :=
  not_isComplete_of_lucasPair (r := 0) (P := 12) (by decide) (by decide) (by decide) (by decide)

private theorem not_isComplete_twelve : ¬IsComplete 12 :=
  not_isComplete_of_lucasPair (r := 0) (P := 24) (by decide) (by decide) (by decide) (by decide)

private theorem not_isComplete_eighteen : ¬IsComplete 18 :=
  not_isComplete_of_lucasPair (r := 5) (P := 24) (by decide) (by decide) (by decide) (by decide)

private theorem not_isComplete_twentyOne : ¬IsComplete 21 :=
  not_isComplete_of_lucasPair (r := 0) (P := 16) (by decide) (by decide) (by decide) (by decide)

private theorem not_isComplete_twentyEight : ¬IsComplete 28 :=
  not_isComplete_of_lucasPair (r := 0) (P := 48) (by decide) (by decide) (by decide) (by decide)

private theorem not_isComplete_fortyNine : ¬IsComplete 49 :=
  not_isComplete_of_lucasPair (r := 5) (P := 112) (by decide) (by decide) (by decide) (by decide)

/-! ### Primes other than `2`, `3` and `7` -/

/-- In `ZMod p` the product of two non-squares is a square. -/
private theorem isSquare_mul_of_not_isSquare {p : ℕ} [Fact p.Prime] {a b : ZMod p}
    (ha : ¬IsSquare a) (hb : ¬IsSquare b) : IsSquare (a * b) := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, (mul_zero 0).symm⟩
  have hb0 : b ≠ 0 := by rintro rfl; exact hb ⟨0, (mul_zero 0).symm⟩
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0), map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr ha, quadraticChar_neg_one_iff_not_isSquare.mpr hb]
  norm_num

private theorem natCast_ne_zero_of_prime {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hpq : p ≠ q) :
    (q : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq Fact.out hq).mp h)

/-- If `5` is a square modulo an odd prime `p`, the Lucas numbers modulo `p` have period
dividing `p - 1`. -/
private theorem lucasNumber_add_sub_one_cast {p : ℕ} [Fact p.Prime] (h2 : p ≠ 2)
    (h5 : IsSquare (5 : ZMod p)) (n : ℕ) :
    (lucasNumber (n + (p - 1)) : ZMod p) = lucasNumber n := by
  obtain ⟨s, hs⟩ := h5
  have two_ne : (2 : ZMod p) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_prime Nat.prime_two h2
  set α : ZMod p := (1 + s) / 2 with hα_def
  set β : ZMod p := (1 - s) / 2 with hβ_def
  have hα : α ^ 2 = α + 1 := by
    rw [hα_def]; field_simp; linear_combination (-1 : ZMod p) * hs
  have hβ : β ^ 2 = β + 1 := by
    rw [hβ_def]; field_simp; linear_combination (-1 : ZMod p) * hs
  have hαβ : α * β = -1 := by
    rw [hα_def, hβ_def]; field_simp; linear_combination hs
  have key : ∀ n, (lucasNumber n : ZMod p) = α ^ n + β ^ n ∧
      (lucasNumber (n + 1) : ZMod p) = α ^ (n + 1) + β ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      have h0 : (lucasNumber 0 : ZMod p) = 2 := by simp [lucasNumber]
      have h1 : (lucasNumber 1 : ZMod p) = 1 := by simp [lucasNumber]
      refine ⟨by rw [h0]; norm_num, ?_⟩
      rw [zero_add, h1, pow_one, pow_one, hα_def, hβ_def, ← add_div,
        show (1 + s) + (1 - s) = (2 : ZMod p) by ring, div_self two_ne]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [lucasNumber_add_two, Nat.cast_add, ih.1, ih.2]
      linear_combination (-α ^ n) * hα + (-β ^ n) * hβ
  have hα0 : α ≠ 0 := by
    intro h; rw [h, zero_mul] at hαβ; exact one_ne_zero (neg_eq_zero.mp hαβ.symm)
  have hβ0 : β ≠ 0 := by
    intro h; rw [h, mul_zero] at hαβ; exact one_ne_zero (neg_eq_zero.mp hαβ.symm)
  rw [(key _).1, (key _).1, pow_add, pow_add, ZMod.pow_card_sub_one_eq_one hα0,
    ZMod.pow_card_sub_one_eq_one hβ0, mul_one, mul_one]

/-- If `5` is not a square modulo `p`, the Lucas numbers miss every residue `t` such that
`t ^ 2 - 4` and `t ^ 2 + 4` are nonzero squares. -/
private theorem lucasNumber_cast_ne {p : ℕ} [Fact p.Prime] (h5 : ¬IsSquare (5 : ZMod p))
    {t a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) (hta : t ^ 2 - 4 = a ^ 2)
    (htb : t ^ 2 + 4 = b ^ 2) (n : ℕ) : (lucasNumber n : ZMod p) ≠ t := by
  intro hn
  have key := congrArg (fun z : ℤ => (z : ZMod p)) (lucasNumber_succ_sq_sub n)
  push_cast at key
  rw [hn] at key
  rcases neg_one_pow_eq_or (ZMod p) (n + 1) with h | h
  · rw [h] at key
    exact h5 ⟨(2 * lucasNumber (n + 1) - t) / b, by
      field_simp; linear_combination (-4 : ZMod p) * key - 5 * htb⟩
  · rw [h] at key
    exact h5 ⟨(2 * lucasNumber (n + 1) - t) / a, by
      field_simp; linear_combination (-4 : ZMod p) * key - 5 * hta⟩

/-- For a prime `p ∉ {2, 3, 7}` modulo which `5` is not a square, there is a residue `t` such
that `t ^ 2 - 4` and `t ^ 2 + 4` are nonzero squares. -/
private theorem exists_sq_sub_four_sq_add_four {p : ℕ} [Fact p.Prime] (h2 : p ≠ 2) (h3 : p ≠ 3)
    (h7 : p ≠ 7) (h5 : ¬IsSquare (5 : ZMod p)) :
    ∃ t a b : ZMod p, a ≠ 0 ∧ b ≠ 0 ∧ t ^ 2 - 4 = a ^ 2 ∧ t ^ 2 + 4 = b ^ 2 := by
  have two_ne : (2 : ZMod p) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_prime Nat.prime_two h2
  have three_ne : (3 : ZMod p) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_prime Nat.prime_three h3
  have seven_ne : (7 : ZMod p) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_prime (by decide : Nat.Prime 7) h7
  have four_ne : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero two_ne two_ne
  by_cases hm1 : IsSquare (-1 : ZMod p)
  · -- `t = 0`
    obtain ⟨i, hi⟩ := hm1
    have hi0 : i ≠ 0 := by rintro rfl; simp at hi
    exact ⟨0, 2 * i, 2, mul_ne_zero two_ne hi0, two_ne, by linear_combination 4 * hi, by ring⟩
  by_cases h2sq : IsSquare (2 : ZMod p)
  · -- `t = 3 / v` with `v ^ 4 = 2`
    obtain ⟨q, hq⟩ := h2sq
    obtain ⟨v, hv⟩ : ∃ v : ZMod p, v ^ 4 = 2 := by
      by_cases hqs : IsSquare q
      · obtain ⟨v, hv⟩ := hqs
        exact ⟨v, by rw [hq, hv]; ring⟩
      · obtain ⟨v, hv⟩ := isSquare_mul_of_not_isSquare hm1 hqs
        exact ⟨v, by linear_combination (-(v * v - q)) * hv - hq⟩
    have hv0 : v ≠ 0 := by rintro rfl; norm_num at hv; exact two_ne hv.symm
    refine ⟨3 / v, (1 - 2 * v ^ 2) / v, (1 + 2 * v ^ 2) / v, ?_, ?_, ?_, ?_⟩
    · refine div_ne_zero (fun h => seven_ne ?_) hv0
      linear_combination (-(1 + 2 * v ^ 2)) * h - 4 * hv
    · refine div_ne_zero (fun h => seven_ne ?_) hv0
      linear_combination (-(1 - 2 * v ^ 2)) * h - 4 * hv
    · field_simp; linear_combination (-4 : ZMod p) * hv
    · field_simp; linear_combination (-4 : ZMod p) * hv
  · -- `-1`, `2` and `5` are non-squares
    have hm2 : IsSquare (-2 : ZMod p) := by
      have := isSquare_mul_of_not_isSquare hm1 h2sq; rwa [neg_one_mul] at this
    have hm5 : IsSquare (-5 : ZMod p) := by
      have := isSquare_mul_of_not_isSquare hm1 h5; rwa [neg_one_mul] at this
    by_cases h3sq : IsSquare (3 : ZMod p)
    · -- `t ^ 2 = -20 / 3`
      obtain ⟨w, hw⟩ : IsSquare (-15 : ZMod p) := by
        have := hm5.mul h3sq; convert this using 1; ring
      obtain ⟨z, hz⟩ : IsSquare (-6 : ZMod p) := by
        have := hm2.mul h3sq; convert this using 1; ring
      have hz0 : z ≠ 0 := by
        rintro rfl
        apply mul_ne_zero two_ne three_ne
        linear_combination (-1 : ZMod p) * hz
      refine ⟨2 * w / 3, 4 * z / 3, 2 * z / 3, ?_, ?_, ?_, ?_⟩
      · exact div_ne_zero (mul_ne_zero four_ne hz0) three_ne
      · exact div_ne_zero (mul_ne_zero two_ne hz0) three_ne
      · field_simp; linear_combination (-4 : ZMod p) * hw + 16 * hz
      · field_simp; linear_combination (-4 : ZMod p) * hw + 4 * hz
    · -- `t ^ 2 = 20 / 3`
      obtain ⟨w, hw⟩ : IsSquare (15 : ZMod p) := by
        have := isSquare_mul_of_not_isSquare h3sq h5; convert this using 1; ring
      obtain ⟨z, hz⟩ : IsSquare (6 : ZMod p) := by
        have := isSquare_mul_of_not_isSquare h2sq h3sq; convert this using 1; ring
      have hz0 : z ≠ 0 := by
        rintro rfl
        apply mul_ne_zero two_ne three_ne
        linear_combination hz
      refine ⟨2 * w / 3, 2 * z / 3, 4 * z / 3, ?_, ?_, ?_, ?_⟩
      · exact div_ne_zero (mul_ne_zero two_ne hz0) three_ne
      · exact div_ne_zero (mul_ne_zero four_ne hz0) three_ne
      · field_simp; linear_combination (-4 : ZMod p) * hw + 4 * hz
      · field_simp; linear_combination (-4 : ZMod p) * hw + 16 * hz

/-- For a prime `p ∉ {2, 3, 7}`, some residue modulo `p` is not a Lucas number. -/
private theorem not_isComplete_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
    (h7 : p ≠ 7) : ¬IsComplete p := by
  have := Fact.mk hp
  by_cases h5 : IsSquare (5 : ZMod p)
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    refine not_isComplete_of_period (P := p - 1) (by omega) (by omega) fun n => ?_
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (lucasNumber_add_sub_one_cast h2 h5 n)
  · obtain ⟨t, a, b, ha, hb, hta, htb⟩ := exists_sq_sub_four_sq_add_four h2 h3 h7 h5
    intro hc
    obtain ⟨n, hn⟩ := hc t.val (ZMod.val_lt t)
    apply lucasNumber_cast_ne h5 ha hb hta htb n
    rw [← ZMod.natCast_mod, hn, ZMod.natCast_zmod_val]

/-! ### Powers of `3` -/

/-- Shifting the Lucas numbers by `N + 1` places. -/
private theorem lucasNumber_add_succ (N n : ℕ) :
    lucasNumber (n + (N + 1)) =
      Nat.fib N * lucasNumber n + Nat.fib (N + 1) * lucasNumber (n + 1) := by
  induction N generalizing n with
  | zero => simp
  | succ N ih =>
    rw [show n + (N + 1 + 1) = n + 1 + (N + 1) by ring, ih (n + 1), Nat.fib_add_two,
      lucasNumber_add_two]
    ring

/-- The Fibonacci numbers `F_{3M+2}` and `F_{3M+3}` in terms of `F_M` and `F_{M+1}`. -/
private theorem fib_three_mul_add_two_add_three (M : ℕ) :
    Nat.fib (3 * M + 2) =
        Nat.fib M ^ 3 + 3 * Nat.fib M * Nat.fib (M + 1) ^ 2 + Nat.fib (M + 1) ^ 3 ∧
      Nat.fib (3 * M + 3) = 3 * Nat.fib M ^ 2 * Nat.fib (M + 1) +
        3 * Nat.fib M * Nat.fib (M + 1) ^ 2 + 2 * Nat.fib (M + 1) ^ 3 := by
  have h1 := Nat.fib_two_mul_add_one M
  have h2 := Nat.fib_two_mul_add_two M
  have h3 : Nat.fib (M + 2) = Nat.fib M + Nat.fib (M + 1) := Nat.fib_add_two
  constructor
  · rw [show 3 * M + 2 = 2 * M + 1 + M + 1 by ring, Nat.fib_add, h1,
      show 2 * M + 1 + 1 = 2 * M + 2 by ring, h2]
    ring
  · rw [show 3 * M + 3 = 2 * M + 1 + (M + 1) + 1 by ring, Nat.fib_add, h1,
      show 2 * M + 1 + 1 = 2 * M + 2 by ring, h2, h3]
    ring

/-- `F_{8·3^k} ≡ 3^(k+1)` and `F_{8·3^k - 1} ≡ 1 + 3^(k+1)` modulo `3^(k+2)`. -/
private theorem fib_eight_mul_three_pow (k : ℕ) : ∃ x y : ℤ,
    (Nat.fib (8 * 3 ^ k) : ℤ) = 3 ^ (k + 1) * (1 + 3 * x) ∧
      (Nat.fib (8 * 3 ^ k - 1) : ℤ) = 1 + 3 ^ (k + 1) * (1 + 3 * y) := by
  induction k with
  | zero => exact ⟨2, 1, by norm_num [Nat.fib_add_two], by norm_num [Nat.fib_add_two]⟩
  | succ k ih =>
    obtain ⟨x, y, hx, hy⟩ := ih
    obtain ⟨M, hM⟩ : ∃ M, 8 * 3 ^ k = M + 1 :=
      ⟨8 * 3 ^ k - 1, by have := Nat.one_le_pow k 3 (by norm_num); omega⟩
    have hN1 : 8 * 3 ^ (k + 1) = 3 * M + 3 := by rw [pow_succ]; omega
    have hN2 : 8 * 3 ^ (k + 1) - 1 = 3 * M + 2 := by omega
    rw [hM] at hx
    rw [hM, Nat.add_sub_cancel] at hy
    obtain ⟨h2, h3⟩ := fib_three_mul_add_two_add_three M
    refine ⟨x + 2 * 3 ^ k * (1 + 3 * x) * (1 + 3 * y) +
        3 * (3 ^ k) ^ 2 * (1 + 3 * x) * (1 + 3 * y) ^ 2 +
        3 ^ k * (1 + 3 * x) ^ 2 * (1 + 3 * 3 ^ k * (1 + 3 * y)) +
        2 * (3 ^ k) ^ 2 * (1 + 3 * x) ^ 3,
      y + 3 ^ k * (1 + 3 * y) ^ 2 + (3 ^ k) ^ 2 * (1 + 3 * y) ^ 3 +
        3 ^ k * (1 + 3 * x) ^ 2 * (1 + 3 * 3 ^ k * (1 + 3 * y)) +
        (3 ^ k) ^ 2 * (1 + 3 * x) ^ 3, ?_, ?_⟩
    · rw [hN1, h3]
      push_cast
      rw [hx, hy]
      ring
    · rw [hN2, h2]
      push_cast
      rw [hx, hy]
      ring

/-- `L_{n + 8·3^k} ≡ L_n + 3^(k+1) L_{n+2}` modulo `3^(k+2)`. -/
private theorem lucasNumber_add_eight_mul_three_pow (k n : ℕ) :
    (lucasNumber (n + 8 * 3 ^ k) : ℤ) ≡ lucasNumber n + 3 ^ (k + 1) * lucasNumber (n + 2)
      [ZMOD 3 ^ (k + 2)] := by
  obtain ⟨x, y, hx, hy⟩ := fib_eight_mul_three_pow k
  obtain ⟨M, hM⟩ : ∃ M, 8 * 3 ^ k = M + 1 :=
    ⟨8 * 3 ^ k - 1, by have := Nat.one_le_pow k 3 (by norm_num); omega⟩
  rw [hM] at hx ⊢
  rw [hM, Nat.add_sub_cancel] at hy
  rw [lucasNumber_add_succ, lucasNumber_add_two]
  push_cast
  rw [hx, hy, Int.modEq_iff_dvd]
  exact ⟨-(y * lucasNumber n + x * lucasNumber (n + 1)), by ring⟩

private theorem lucasNumber_add_eight_mul_three_pow_modEq_three (k n : ℕ) :
    (lucasNumber (n + 8 * 3 ^ k) : ℤ) ≡ lucasNumber n [ZMOD 3] := by
  refine ((lucasNumber_add_eight_mul_three_pow k n).of_dvd
    (dvd_pow_self 3 (by omega : k + 2 ≠ 0))).trans ?_
  rw [Int.modEq_iff_dvd]
  exact ⟨-(3 ^ k * lucasNumber (n + 2)), by ring⟩

/-- Every residue modulo `3^(k+1)` is attained by some `L_n` with `3 ∤ L_{n+2}`. -/
private theorem exists_lucasNumber_modEq_three_pow (k : ℕ) (r : ℤ) :
    ∃ n, (lucasNumber n : ℤ) ≡ r [ZMOD 3 ^ (k + 1)] ∧ ¬(3 : ℤ) ∣ lucasNumber (n + 2) := by
  induction k generalizing r with
  | zero =>
    have hL1 : lucasNumber 1 = 1 := rfl
    have hL2 : lucasNumber 2 = 3 := rfl
    have hL3 : lucasNumber 3 = 4 := rfl
    have hL4 : lucasNumber 4 = 7 := rfl
    have hL5 : lucasNumber 5 = 11 := rfl
    have hL7 : lucasNumber 7 = 29 := rfl
    simp only [Int.ModEq, zero_add, pow_one]
    rcases (by omega : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2) with h | h | h
    · exact ⟨2, by rw [hL2]; omega, by rw [hL4]; omega⟩
    · exact ⟨1, by rw [hL1]; omega, by rw [hL3]; omega⟩
    · exact ⟨5, by rw [hL5]; omega, by rw [hL7]; omega⟩
  | succ k ih =>
    obtain ⟨n, hn, hn3⟩ := ih r
    obtain ⟨c, hc⟩ := hn.dvd
    set u : ℤ := ((lucasNumber (n + 2) : ℕ) : ℤ) with hu
    -- the two shifted indices
    have h1 := lucasNumber_add_eight_mul_three_pow k n
    have h2 : (lucasNumber (n + 8 * 3 ^ k + 8 * 3 ^ k) : ℤ) ≡
        lucasNumber n + 2 * 3 ^ (k + 1) * u [ZMOD 3 ^ (k + 2)] := by
      have h3 := lucasNumber_add_eight_mul_three_pow k (n + 8 * 3 ^ k)
      have h4 := (lucasNumber_add_eight_mul_three_pow_modEq_three k (n + 2)).mul_left'
        (c := 3 ^ (k + 1))
      rw [show (3 : ℤ) ^ (k + 1) * 3 = 3 ^ (k + 2) by ring] at h4
      calc (lucasNumber (n + 8 * 3 ^ k + 8 * 3 ^ k) : ℤ)
          ≡ lucasNumber (n + 8 * 3 ^ k) + 3 ^ (k + 1) * lucasNumber (n + 8 * 3 ^ k + 2)
            [ZMOD 3 ^ (k + 2)] := h3
        _ ≡ (lucasNumber n + 3 ^ (k + 1) * u) + 3 ^ (k + 1) * u [ZMOD 3 ^ (k + 2)] := by
          rw [show n + 8 * 3 ^ k + 2 = n + 2 + 8 * 3 ^ k by ring]
          exact h1.add h4
        _ = lucasNumber n + 2 * 3 ^ (k + 1) * u := by ring
    -- a congruence `c ≡ j * u [ZMOD 3]` gives `L_n + j 3^(k+1) u ≡ r [ZMOD 3^(k+2)]`
    have lift : ∀ j : ℤ, c ≡ j * u [ZMOD 3] →
        (lucasNumber n : ℤ) + j * 3 ^ (k + 1) * u ≡ r [ZMOD 3 ^ (k + 1 + 1)] := by
      intro j hj
      obtain ⟨d, hd⟩ := hj.dvd
      rw [Int.modEq_iff_dvd]
      exact ⟨-d, by linear_combination hc - 3 ^ (k + 1) * hd⟩
    have hu3 : ¬(3 : ℤ) ∣ u := hn3
    have hcases : c ≡ 0 * u [ZMOD 3] ∨ c ≡ 1 * u [ZMOD 3] ∨ c ≡ 2 * u [ZMOD 3] := by
      simp only [Int.ModEq]
      rcases (by omega : u % 3 = 1 ∨ u % 3 = 2) with hu' | hu' <;>
        rcases (by omega : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2) with hc' | hc' | hc' <;>
        omega
    rcases hcases with hj | hj | hj
    · refine ⟨n, ?_, hn3⟩
      simpa using lift 0 hj
    · refine ⟨n + 8 * 3 ^ k, h1.trans (by simpa using lift 1 hj), ?_⟩
      rw [show n + 8 * 3 ^ k + 2 = n + 2 + 8 * 3 ^ k by ring]
      exact fun h => hu3 ((lucasNumber_add_eight_mul_three_pow_modEq_three k (n + 2)).dvd_iff.mp h)
    · refine ⟨n + 8 * 3 ^ k + 8 * 3 ^ k, h2.trans (by simpa [mul_assoc] using lift 2 hj), ?_⟩
      rw [show n + 8 * 3 ^ k + 8 * 3 ^ k + 2 = n + 2 + 8 * 3 ^ k + 8 * 3 ^ k by ring]
      intro h
      apply hu3
      exact ((lucasNumber_add_eight_mul_three_pow_modEq_three k (n + 2 + 8 * 3 ^ k)).trans
        (lucasNumber_add_eight_mul_three_pow_modEq_three k (n + 2))).dvd_iff.mp h

private theorem isComplete_three_pow {k : ℕ} (hk : 1 ≤ k) : IsComplete (3 ^ k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  intro r hr
  obtain ⟨n, hn, -⟩ := exists_lucasNumber_modEq_three_pow j r
  refine ⟨n, ?_⟩
  have h : lucasNumber n ≡ r [MOD 3 ^ (j + 1)] := Int.natCast_modEq_iff.mp (by exact_mod_cast hn)
  rw [Nat.ModEq, Nat.mod_eq_of_lt hr] at h
  exact h

/-! ### The classification -/

private theorem eq_of_isComplete {m : ℕ} (hm : 1 < m) (hc : IsComplete m) :
    m = 2 ∨ m = 4 ∨ m = 6 ∨ m = 7 ∨ m = 14 ∨ ∃ k : ℕ, 1 ≤ k ∧ m = 3 ^ k := by
  have hdvd : ∀ d, d ∣ m → IsComplete d := fun d hd => isComplete_of_dvd hc hd (by omega)
  have hprime : ∀ p, p.Prime → p ∣ m → p = 2 ∨ p = 3 ∨ p = 7 := by
    intro p hp hpm
    by_contra h
    simp only [not_or] at h
    exact not_isComplete_prime hp h.1 h.2.1 h.2.2 (hdvd p hpm)
  have h8 : ¬8 ∣ m := fun h => not_isComplete_eight (hdvd 8 h)
  have h12 : ¬12 ∣ m := fun h => not_isComplete_twelve (hdvd 12 h)
  have h18 : ¬18 ∣ m := fun h => not_isComplete_eighteen (hdvd 18 h)
  have h21 : ¬21 ∣ m := fun h => not_isComplete_twentyOne (hdvd 21 h)
  have h28 : ¬28 ∣ m := fun h => not_isComplete_twentyEight (hdvd 28 h)
  have h49 : ¬49 ∣ m := fun h => not_isComplete_fortyNine (hdvd 49 h)
  obtain ⟨a, m₁, h2m₁, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) 2 (by norm_num)
  have hm₁ : m₁ ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨b, m₂, h3m₂, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm₁ 3 (by norm_num)
  have hm₂ : m₂ ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨c, m₃, h7m₃, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm₂ 7 (by norm_num)
  have hm₃ : m₃ = 1 := by
    by_contra hne
    have hq := Nat.minFac_prime hne
    have hqm₃ : m₃.minFac ∣ m₃ := Nat.minFac_dvd m₃
    rcases hprime _ hq (hqm₃.trans (((dvd_mul_left m₃ (7 ^ c)).mul_left (3 ^ b)).mul_left (2 ^ a)))
      with h | h | h
    · exact h2m₁ (h ▸ hqm₃.trans ((dvd_mul_left m₃ (7 ^ c)).mul_left (3 ^ b)))
    · exact h3m₂ (h ▸ hqm₃.trans (dvd_mul_left m₃ (7 ^ c)))
    · exact h7m₃ (h ▸ hqm₃)
  subst hm₃
  have ha : a ≤ 2 := by
    by_contra h
    exact h8 ((pow_dvd_pow 2 (by omega : 3 ≤ a)).trans (Dvd.intro _ rfl))
  have hc : c ≤ 1 := by
    by_contra h
    exact h49 ((pow_dvd_pow 7 (by omega : 2 ≤ c)).trans
      (((dvd_mul_right (7 ^ c) 1).mul_left (3 ^ b)).mul_left (2 ^ a)))
  interval_cases a <;> interval_cases c
  · rcases b with _ | b
    · norm_num at hm
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨b + 1, by omega, by ring⟩))))
  · rcases b with _ | b
    · right; right; right; left; norm_num
    · exact (h21 ⟨3 ^ b, by ring⟩).elim
  · rcases b with _ | _ | b
    · left; norm_num
    · right; right; left; norm_num
    · exact (h18 ⟨3 ^ b, by ring⟩).elim
  · rcases b with _ | b
    · right; right; right; right; left; norm_num
    · exact (h21 ⟨2 * 3 ^ b, by ring⟩).elim
  · rcases b with _ | b
    · right; left; norm_num
    · exact (h12 ⟨3 ^ b, by ring⟩).elim
  · exact (h28 ⟨3 ^ b, by ring⟩).elim

/--
**Avila–Chen theorem on Lucas numbers modulo $m$.** Let $L_n$ denote the Lucas numbers. For every
integer $m > 1$, every residue modulo $m$ is attained by the Lucas numbers (for every $r$ with
$0 \le r < m$ there is $n \ge 0$ with $L_n \equiv r \pmod m$) if and only if
$m \in \{2, 4, 6, 7, 14\}$ or $m = 3^k$ for some integer $k \ge 1$.

Source: Brandon Avila and Yongyi Chen, On Moduli For Which the Lucas Numbers Contain a Complete
Residue System, Fibonacci Quarterly 51(2) (2013), 151–152,
https://doi.org/10.1080/00150517.2013.12427958. Moved from
`OpenConjectures/NumberTheory/LucasNumbersModuloM`.
-/
theorem Statement_holds : Statement := by
  intro m hm
  refine ⟨eq_of_isComplete hm, ?_⟩
  rintro (rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩)
  · exact isComplete_two
  · exact isComplete_four
  · exact isComplete_six
  · exact isComplete_seven
  · exact isComplete_fourteen
  · exact isComplete_three_pow hk

end MathlibExt.NumberTheory.LucasNumbersModuloMWanted
