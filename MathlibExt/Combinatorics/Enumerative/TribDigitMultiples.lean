/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Fin
import MathlibExt.Combinatorics.Additive.ConsecutiveZeroSum

/-!
# Tribbinary and Tribternary multiples

A nonempty zero-sum block of consecutive powers of `b ^ 2` modulo `n` gives a positive
multiple of `n` whose base-`b` digits are zeros and separated ones.

## References

- Eric Chen, Adam Ge, Andrew Kalashnikov, Ella Kim, Evin Liang, Mira Lubashev, Matthew Qian,
  Rohith Raghavan, Benjamin Taycher, Samuel Wang and Tanya Khovanova,
  *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*,
  Journal of Integer Sequences 28 (2025), Article 25.5.4, pp. 1–31, §7.6, Corollary 23.
  <https://cs.uwaterloo.ca/journals/JIS/VOL28/Khovanova/khova43.html>
- Rémy Sigrist, [OEIS A300867](https://oeis.org/A300867) (2018), the pigeonhole argument
  for Fibbinary multiples cited in §7.6.
- Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
  of ℤₙ*, INTEGERS 24 (2024), Article A38, pp. 1–16, Theorem 3.1, for the consecutive zero-sum
  result. <https://math.colgate.edu/~integers/y38/y38.pdf>
-/

namespace MetaMathlibExt

open Finset

-- The alternating word with `k + 1` ones, ending in its most significant one.
private def alternatingOnes : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => 1 :: 0 :: alternatingOnes k

private theorem mem_alternatingOnes_le_one {k d : ℕ} (hd : d ∈ alternatingOnes k) : d ≤ 1 := by
  induction k with
  | zero =>
    simp [alternatingOnes] at hd
    exact hd.le
  | succ k ih =>
    simp only [alternatingOnes, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · exact le_rfl
    · exact Nat.zero_le _
    · exact ih hd

private theorem getLast_alternatingOnes (k : ℕ) (h : alternatingOnes k ≠ []) :
    (alternatingOnes k).getLast h = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : alternatingOnes k ≠ [] := by cases k <;> simp [alternatingOnes]
    change (1 :: 0 :: alternatingOnes k).getLast _ = 1
    rw [List.getLast_cons (by simp), List.getLast_cons hk, ih hk]

private theorem no_adjacent_ones_alternatingOnes (k : ℕ) : ¬ [1, 1] <:+: alternatingOnes k := by
  induction k with
  | zero => simp [alternatingOnes, List.infix_cons_iff]
  | succ k ih => simp [alternatingOnes, List.infix_cons_iff, ih]

private theorem no_adjacent_ones_replicate_zero_append {w : List ℕ} (hw : ¬ [1, 1] <:+: w)
    (k : ℕ) : ¬ [1, 1] <:+: List.replicate k 0 ++ w := by
  induction k with
  | zero => simpa using hw
  | succ k ih => simpa [List.replicate_succ, List.infix_cons_iff] using ih

private theorem ofDigits_alternatingOnes (b k : ℕ) :
    Nat.ofDigits b (alternatingOnes k) = ∑ i ∈ range (k + 1), (b ^ 2) ^ i := by
  induction k with
  | zero => simp [alternatingOnes]
  | succ k ih =>
    rw [alternatingOnes, Nat.ofDigits_cons, Nat.ofDigits_cons, zero_add, ← mul_assoc, ← pow_two,
      ih, mul_sum, sum_range_succ' (fun i : ℕ => (b ^ 2) ^ i) (k + 1)]
    simp only [pow_zero, pow_succ', add_comm]

private theorem exists_multiple_no_adjacent_ones (b n : ℕ) (hb : 1 < b) (hn : 0 < n) :
    ∃ m, 0 < m ∧ n ∣ m ∧ (∀ d ∈ Nat.digits b m, d ≤ 1) ∧ ¬ [1, 1] <:+: Nat.digits b m := by
  have : NeZero n := ⟨hn.ne'⟩
  have hblock := (consecutive_constant_eq_card (ZMod n)).1.2
  rw [ZMod.card] at hblock
  obtain ⟨s, t, hst, a, ha, hsum⟩ := hblock (fun i => ((b : ZMod n) ^ 2) ^ (i : ℕ))
  have hdvd : n ∣ ∑ i ∈ Icc (s : ℕ) (t : ℕ), (b ^ 2) ^ i := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [← Fin.map_valEmbedding_Icc s t, sum_map, Nat.cast_sum]
    refine (sum_congr rfl fun i hi => ?_).trans hsum
    rw [show a i = 1 from ha i hi, one_zsmul]
    simp only [Fin.valEmbedding_apply, Nat.cast_pow]
  let k := (t : ℕ) - (s : ℕ)
  let m := b ^ (2 * (s : ℕ)) * Nat.ofDigits b (alternatingOnes k)
  have hval : 0 < Nat.ofDigits b (alternatingOnes k) := by
    cases k <;> simp [alternatingOnes, Nat.ofDigits_cons]
  have hm : 0 < m := Nat.mul_pos (pow_pos (Nat.zero_lt_of_lt hb) _) hval
  have heq : (∑ i ∈ Icc (s : ℕ) (t : ℕ), (b ^ 2) ^ i) = m := by
    have hlen : (t : ℕ) + 1 - (s : ℕ) = k + 1 := by
      have : (s : ℕ) ≤ (t : ℕ) := hst
      dsimp [k]
      omega
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, hlen]
    simp only [m, ofDigits_alternatingOnes, pow_mul, mul_sum, pow_add]
  refine ⟨m, hm, heq ▸ hdvd, ?_⟩
  have hdigits : Nat.digits b m = List.replicate (2 * (s : ℕ)) 0 ++ alternatingOnes k := by
    rw [Nat.digits_base_pow_mul hb hval]
    refine congrArg (List.replicate (2 * (s : ℕ)) 0 ++ ·) (Nat.digits_ofDigits b hb _ ?_ ?_)
    · intro d hd
      exact (mem_alternatingOnes_le_one hd).trans_lt hb
    · intro h
      rw [getLast_alternatingOnes k h]
      exact one_ne_zero
  rw [hdigits]
  refine ⟨?_, no_adjacent_ones_replicate_zero_append (no_adjacent_ones_alternatingOnes k) _⟩
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact (List.eq_of_mem_replicate hd).le.trans (Nat.zero_le _)
  · exact mem_alternatingOnes_le_one hd

/-- **Tribbinary and Tribternary multiples.** Every positive integer $n$ has a positive
multiple whose binary digits contain no three consecutive $1$s (a Tribbinary number), and a
positive multiple whose base-$3$ digits are all $0$ or $1$ with no three consecutive $1$s (a
Tribternary number).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Corollary 23 (`jis-2025-25.5.4-cor-23`). -/
public theorem exists_tribbinary_and_tribternary_multiple (n : ℕ) (hn : 0 < n) :
    (∃ m, 0 < m ∧ n ∣ m ∧ ¬ [1, 1, 1] <:+: Nat.digits 2 m) ∧
      ∃ m, 0 < m ∧ n ∣ m ∧ (∀ e ∈ Nat.digits 3 m, e ≤ 1) ∧ ¬ [1, 1, 1] <:+: Nat.digits 3 m := by
  have hprefix : [1, 1] <+: ([1, 1, 1] : List ℕ) := ⟨[1], rfl⟩
  obtain ⟨m₂, hm₂, hd₂, -, h₂⟩ := exists_multiple_no_adjacent_ones 2 n (by decide) hn
  obtain ⟨m₃, hm₃, hd₃, hdigits₃, h₃⟩ := exists_multiple_no_adjacent_ones 3 n (by decide) hn
  exact ⟨⟨m₂, hm₂, hd₂, fun h => h₂ (hprefix.isInfix.trans h)⟩,
    ⟨m₃, hm₃, hd₃, hdigits₃, fun h => h₃ (hprefix.isInfix.trans h)⟩⟩

end MetaMathlibExt
