/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.NumberTheory.PolygonalNumber
public import MathlibExt.NumberTheory.PracticalNumber
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Lift
import Mathlib.Tactic.LinearCombination

/-! # Sums of practical and polygonal numbers -/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **Square roots modulo powers of two.** For all natural numbers $m > 0$ and $n > 0$ there is
a natural number $x$ with $1 \le x \le 2^m - 1$ and $x^2 \equiv 8n + 1 \pmod{2^{m+2}}$.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 3
(arXiv Lemma 3.1; `jis-2024-24.5.1-lem-3`). -/
public theorem exists_sq_modEq_eight_mul_add_one (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ x : ℕ, 1 ≤ x ∧ x ≤ 2 ^ m - 1 ∧ x ^ 2 ≡ 8 * n + 1 [MOD 2 ^ (m + 2)] := by
  -- Write the odd root as 2a + 1 and keep the signed quotient of the square error.
  have liftRoot (k : ℕ) : ∃ a q : ℤ, 0 ≤ a ∧ a < 2 ^ k ∧
      8 * (n : ℤ) + 1 - (2 * a + 1) ^ 2 = 8 * 2 ^ k * q := by
    induction k with
    | zero => exact ⟨0, n, by decide, by decide, by simp⟩
    | succ k ih =>
      obtain ⟨a, q, ha, hlt, hq⟩ := ih
      rw [pow_succ]
      obtain ⟨t, rfl | rfl⟩ := Int.even_or_odd' q
      · exact ⟨a, t, ha, by omega, by linear_combination hq⟩
      · -- Reflect about 2^(k+1). The squares differ by 8·2^k times the odd number 2·2^k-2a-1.
        refine ⟨2 * 2 ^ k - 1 - a, t + 1 + a - 2 ^ k, by omega, by omega, ?_⟩
        linear_combination hq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨a, q, ha, hlt, hq⟩ := liftRoot k
  lift a to ℕ using ha
  have hbound : a < 2 ^ k := by exact_mod_cast hlt
  refine ⟨2 * a + 1, by omega, ?_, Nat.modEq_iff_dvd.mpr ⟨q, ?_⟩⟩
  · rw [pow_succ]
    omega
  · push_cast
    rw [show k.succ + 2 = k + 3 from rfl, pow_add]
    linear_combination hq

open Polynomial in
/-- **Sums of two polygonal numbers modulo an odd prime.** For a natural number $s > 3$ and a
natural number $x$, let $P_s(x) = (s-2)\binom{x}{2} + x$ be the $x$-th $s$-gonal number. For
every odd prime $p$ and every natural number $n > 0$ there are natural numbers $x, y > 0$ with
$P_s(x) + P_s(y) \equiv n \pmod{p}$.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 6
(arXiv Lemma 4.1; `jis-2024-24.5.1-lem-6`). -/
public theorem exists_polygonal_add_polygonal_modEq_prime (p n s : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 0 < n) (hs : 3 < s) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ Nat.polygonalNumber s x + Nat.polygonalNumber s y ≡ n [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (2 : ZMod p) :=
    NeZero.of_not_dvd (R := ZMod p) ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).not.mpr hp2)
  let a : ZMod p := (s - 2) / 2
  have hP (k : ℕ) : (Nat.polygonalNumber s k : ZMod p) =
      a * k ^ 2 + (1 - a) * k := by
    rw [Nat.polygonalNumber, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ s),
      Nat.cast_two, Nat.cast_choose_two]
    dsimp [a]
    ring
  by_cases ha : a = 0
  · -- The polygonal polynomial reduces to the identity.
    refine ⟨n, p, hn, hp.pos, (ZMod.natCast_eq_natCast_iff ..).mp ?_⟩
    simp [Nat.cast_add, hP, ha]
  · -- Two quadratic images in a field of odd order must intersect after reflection.
    let f (c : ZMod p) := C a * X ^ 2 + C (1 - a) * X + C c
    have hdeg (c : ZMod p) : (f c).degree = 2 := degree_quadratic ha
    obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic (hdeg 0) (hdeg (-n))
      (by rw [ZMod.card]; exact hp.eq_two_or_odd.resolve_left hp2)
    refine ⟨x.val + p, y.val + p, Nat.add_pos_right _ hp.pos, Nat.add_pos_right _ hp.pos,
      (ZMod.natCast_eq_natCast_iff ..).mp ?_⟩
    simp only [Nat.cast_add, hP, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
    rw [← sub_eq_zero]
    simpa [f, sub_eq_add_neg, ← add_assoc] using hxy

/-- **Quadratic upper bound for polygonal numbers.** For a natural number $s > 3$ and a natural
number $x$, let $P_s(x) = (s-2)\binom{x}{2} + x$ be the $x$-th $s$-gonal number. For every natural
number $c$ there is a natural number $A$ such that $2 P_s(2cx) \le A x^2$ for every natural
number $x \ge 1$.

The paper states this only for one specific prime $c$, the prime chosen in Lemma 9 (arXiv
Lemma 4.4), and for real $x$; here $c$ is an arbitrary natural number and $x$ is a natural number.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 10
(arXiv Lemma 4.5; `jis-2024-24.5.1-lem-10`). -/
public theorem exists_two_polygonal_two_mul_le_mul_sq (s c : ℕ) (hs : 3 < s) :
    ∃ A : ℕ, ∀ x : ℕ, 1 ≤ x → 2 * Nat.polygonalNumber s (2 * c * x) ≤ A * x ^ 2 := by
  refine ⟨(s - 2) * (2 * c) ^ 2, fun x _ ↦ ?_⟩
  let n := 2 * c * x
  calc
    2 * Nat.polygonalNumber s n = (s - 2) * (2 * n.choose 2) + 2 * n := by
      unfold Nat.polygonalNumber
      ring
    _ ≤ (s - 2) * (2 * n.choose 2) + (s - 2) * n :=
      Nat.add_le_add_left (Nat.mul_le_mul_right n (by omega)) _
    _ = (s - 2) * Nat.polygonalNumber 4 n := (Nat.mul_add ..).symm
    _ = (s - 2) * (2 * c) ^ 2 * x ^ 2 := by
      simp only [Nat.polygonalNumber_four, n, mul_pow, mul_assoc]

/-- **Practical numbers divisible by neither 3 nor 4.** If $q$ is a practical number that is
divisible by neither $3$ nor $4$, then $q = 1$ or $q = 2$.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 11
(arXiv Lemma 4.6; `jis-2024-24.5.1-lem-11`). -/
public theorem isPracticalNumber_eq_one_or_two (q : ℕ) (hq : IsPracticalNumber q)
    (h3 : ¬ 3 ∣ q) (h4 : ¬ 4 ∣ q) :
    q = 1 ∨ q = 2 := by
  obtain ⟨hqpos, hrep⟩ := hq
  by_cases hq4 : 4 ≤ q
  · obtain ⟨s, hs, hsum⟩ := hrep 4 (by decide) hq4
    -- Only 1 and 2 can occur in a sum of distinct divisors equal to 4.
    have hsub : s ⊆ {1, 2} := by
      intro d hd
      have hpos := Nat.pos_of_mem_divisors (hs hd)
      have hdvd := Nat.dvd_of_mem_divisors (hs hd)
      have hle : d ≤ 4 := hsum ▸ Finset.single_le_sum (fun i _ ↦ Nat.zero_le i) hd
      have hd3 : d ≠ 3 := fun e ↦ h3 (e ▸ hdvd)
      have hd4 : d ≠ 4 := fun e ↦ h4 (e ▸ hdvd)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hle := Finset.sum_le_sum_of_subset (f := fun d : ℕ ↦ d) hsub
    simp [hsum] at hle
  · omega

end MetaMathlibExt
