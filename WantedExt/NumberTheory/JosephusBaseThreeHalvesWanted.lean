/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Nth
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.JosephusFunction
import Mathlib.Tactic

namespace MetaMathlibExt

@[expose] public section

/-- The zero-indexed increasing enumeration of positive fixed points of `josephus 3`;
`josephusThreeFixedPoint ℓ` is the paper's `n_p^{(ℓ+1)}`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public noncomputable def josephusThreeFixedPoint (ℓ : ℕ) : ℕ :=
  Nat.nth (fun n => 1 ≤ n ∧ josephus 3 n = n) ℓ

/-- The number of pure high extremal points strictly between consecutive fixed points;
this is the paper's `m̄_ℓ` with the same one-place index shift as
`josephusThreeFixedPoint`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public noncomputable def josephusThreeGap (ℓ : ℕ) : ℕ :=
  ((Finset.Ioo (josephusThreeFixedPoint ℓ) (josephusThreeFixedPoint (ℓ + 1))).filter
    (fun n => josephus 3 n + 1 = n)).card

/-- The little-endian base-`3/2` digits: a positive `N` emits
`d = 2 * N % 3` and continues with `(2 * N - d) / 3`, while zero emits no digits.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public def baseThreeHalvesDigits : ℕ → List ℕ
  | 0 => []
  | N + 1 =>
    let d := 2 * (N + 1) % 3
    d :: baseThreeHalvesDigits ((2 * (N + 1) - d) / 3)
  termination_by N => N
  decreasing_by omega

/-- The rational positional value of a little-endian digit list, before the paper's
factor of one half is applied.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
private def baseThreeHalvesValue (digits : List ℕ) : ℚ :=
  ∑ i : Fin digits.length, digits[i] * (3 / 2 : ℚ) ^ (i : ℕ)

/-- Prepending the least-significant digit contributes that digit and shifts every
old digit by one power of `3/2`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
private theorem baseThreeHalvesValue_cons (d : ℕ) (digits : List ℕ) :
    baseThreeHalvesValue (d :: digits) =
      d + (3 / 2 : ℚ) * baseThreeHalvesValue digits := by
  unfold baseThreeHalvesValue
  simp only [List.length_cons]
  rw [Fin.sum_univ_succ]
  congr 1
  · simp
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (digits.get i : ℚ) * (3 / 2 : ℚ) ^ (i + 1 : ℕ) =
      (3 / 2 : ℚ) * ((digits.get i : ℚ) * (3 / 2 : ℚ) ^ (i : ℕ))
    rw [pow_succ]
    ring

/-- The emitted base-`3/2` digits of `4` are `[2, 1, 2]` in little-endian order,
corresponding to the paper's `(212)_{3/2}`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem baseThreeHalvesDigits_four : baseThreeHalvesDigits 4 = [2, 1, 2] := by
  norm_num [baseThreeHalvesDigits]

/-- The emitted base-`3/2` digits of `13` are `[2, 1, 1, 0, 1, 2]` in
little-endian order, corresponding to the paper's `(210112)_{3/2}`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem baseThreeHalvesDigits_thirteen :
    baseThreeHalvesDigits 13 = [2, 1, 1, 0, 1, 2] := by
  norm_num [baseThreeHalvesDigits]

/-- The positional value of the emitted little-endian digits is twice the encoded
natural number, accounting for the paper's factor of one half.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
private theorem baseThreeHalvesValue_digits (N : ℕ) :
    baseThreeHalvesValue (baseThreeHalvesDigits N) = 2 * (N : ℚ) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    cases N with
    | zero => simp [baseThreeHalvesDigits, baseThreeHalvesValue]
    | succ n =>
      let d := 2 * (n + 1) % 3
      let q := (2 * (n + 1) - d) / 3
      have hq : q < n + 1 := by
        dsimp [q, d]
        omega
      have hn : 2 * (n + 1) = 3 * q + d := by
        dsimp [q, d]
        omega
      rw [baseThreeHalvesDigits]
      change baseThreeHalvesValue (d :: baseThreeHalvesDigits q) = _
      rw [baseThreeHalvesValue_cons, ih q hq]
      have hnq : (2 * (n + 1) : ℚ) = 3 * q + d := by
        exact_mod_cast hn
      norm_num [Nat.cast_add] at hnq ⊢
      linarith

/-- For every natural `N`, the rational positional sum of its little-endian
base-`3/2` digits is exactly `2 * N`, equivalently the paper's expansion has value `N`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem baseThreeHalvesDigits_value (N : ℕ) :
    2 * (N : ℚ) =
      ∑ i : Fin (baseThreeHalvesDigits N).length,
        (baseThreeHalvesDigits N)[i] * (3 / 2 : ℚ) ^ (i : ℕ) := by
  exact (baseThreeHalvesValue_digits N).symm

/-- Every digit emitted by `baseThreeHalvesDigits` belongs to `{0, 1, 2}`, formally
expressed by the strict bound `d < 3`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem baseThreeHalvesDigits_lt_three (N d : ℕ)
    (hd : d ∈ baseThreeHalvesDigits N) : d < 3 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    cases N with
    | zero => simp [baseThreeHalvesDigits] at hd
    | succ n =>
      let head := 2 * (n + 1) % 3
      let q := (2 * (n + 1) - head) / 3
      have hq : q < n + 1 := by
        dsimp [q, head]
        omega
      simp only [baseThreeHalvesDigits, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact Nat.mod_lt _ (by omega)
      · exact ih q hq hd

/-- The first zero-indexed positive fixed point is `1`, the paper's `n_p^{(1)}`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem josephusThreeFixedPoint_zero : josephusThreeFixedPoint 0 = 1 := by
  change Nat.nth (fun n => 1 ≤ n ∧ josephus 3 n = n) 0 = 1
  have hp : 1 ≤ 1 ∧ josephus 3 1 = 1 := by decide
  have hc : Nat.count (fun n => 1 ≤ n ∧ josephus 3 n = n) 1 = 0 := by decide
  rw [← hc]
  exact Nat.nth_count hp

/-- The second zero-indexed positive fixed point is `2`, the paper's `n_p^{(2)}`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem josephusThreeFixedPoint_one : josephusThreeFixedPoint 1 = 2 := by
  change Nat.nth (fun n => 1 ≤ n ∧ josephus 3 n = n) 1 = 2
  have hp : 1 ≤ 2 ∧ josephus 3 2 = 2 := by decide
  have hc : Nat.count (fun n => 1 ≤ n ∧ josephus 3 n = n) 2 = 1 := by decide
  rw [← hc]
  exact Nat.nth_count hp

/-- The third zero-indexed positive fixed point is `13`, the paper's `n_p^{(3)}`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem josephusThreeFixedPoint_two : josephusThreeFixedPoint 2 = 13 := by
  change Nat.nth (fun n => 1 ≤ n ∧ josephus 3 n = n) 2 = 13
  have hp : 1 ≤ 13 ∧ josephus 3 13 = 13 := by decide
  have hc : Nat.count (fun n => 1 ≤ n ∧ josephus 3 n = n) 13 = 2 := by decide
  rw [← hc]
  exact Nat.nth_count hp

/-- Between the fixed points `2` and `13` there are exactly three pure high extremal
points, so the zero-indexed gap `josephusThreeGap 1` is the paper's `m̄_2 = 3`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem josephusThreeGap_one : josephusThreeGap 1 = 3 := by
  simp only [josephusThreeGap, josephusThreeFixedPoint_one,
    josephusThreeFixedPoint_two, Nat.reduceAdd]
  decide

/-- Theorem 1(i): with `D` and `E` the little-endian base-`3/2` digit lists of
consecutive zero-indexed fixed points and `m` their counted pure-high-extremal gap,
`m = 0` implies that `E` is obtained by prepending `1` to `D`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem_wanted josephusThreeFixedPoint_digits_of_gap_zero (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    m = 0 → E = 1 :: D

/-- Theorem 1(ii): with `D`, `E`, and `m` as in Theorem 1(i), `m = 1` implies
that `E` is obtained by prepending little-endian digits `[2, 0]` to `D`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem_wanted josephusThreeFixedPoint_digits_of_gap_one (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    m = 1 → E = [2, 0] ++ D

/-- Theorem 1(iii): with `D`, `E`, and `m` as in Theorem 1(i), `2 ≤ m` implies
that `E` starts with `2`, then `m - 1` ones and a zero, followed by `D`; this is
the little-endian form of the paper's appended `0`, ones, and `2`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem_wanted josephusThreeFixedPoint_digits_of_gap_at_least_two (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    2 ≤ m → E = 2 :: List.replicate (m - 1) 1 ++ 0 :: D

/-- Theorem 1(iv): with `D`, `E`, and `m` as in Theorem 1(i), the next fixed point's
digit count is the current count plus the pure-high-extremal gap and one.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem_wanted josephusThreeFixedPoint_digits_length (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    E.length = D.length + m + 1

end

end MetaMathlibExt
