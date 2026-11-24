/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import MathlibExt.Combinatorics.Enumerative.Partition.RookDecomposition
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Periodicity of the max-rook partition count

The generating function gives the change in the number of partitions with max-rook number
three when the size increases by three. Iterating gives periodicity modulo any natural
number `p ≥ 2` with period `3 * p`.
-/

namespace MetaMathlibExt

namespace maxRookPartitionCount_three_modEq

open PowerSeries

/-- After size nine the three-step difference is linear in the size. -/
private theorem step (n : ℕ) (hn : 9 < n) :
    (maxRookPartitionCount 3 (n + 3) : ℤ) - maxRookPartitionCount 3 n = 4 * n - 9 := by
  let F := mk fun k ↦ (maxRookPartitionCount 3 k : ℤ)
  let L := mk fun k : ℕ ↦ (k : ℤ) + 1
  have hinv : L * (1 - X) ^ 2 = 1 := by
    simpa [L, add_comm] using mk_add_choose_mul_one_sub_pow_eq_one ℤ 1
  let shift (k : ℕ) := X ^ k * L
  -- Cancel the square of 1 - X in the denominator, leaving the three-step difference.
  have hF : F - X ^ 3 * F =
      shift 6 + 2 • shift 7 + shift 8 + 2 • shift 9 - shift 10 - shift 12 -
        shift 13 + shift 14 := calc
    _ = (L * (1 - X) ^ 2) * (F - X ^ 3 * F) := by rw [hinv, one_mul]
    _ = L * ((1 - X) ^ 3 * (1 + X + X ^ 2) * F) := by ring
    _ = _ := by
      rw [maxRookPartitionCount_three_genFun]
      simp only [shift, two_nsmul]
      ring
  -- At n = 10 the degree-14 term contributes zero, as the linear expression predicts.
  have hshift (k : ℕ) (hk : k ≤ 14) : coeff (n + 3) (shift k) = (n : ℤ) + 4 - k := by
    simp only [shift, coeff_X_pow_mul', L, coeff_mk]
    split <;> omega
  have h := congrArg (coeff (n + 3)) hF
  simp (disch := decide) only [map_sub, map_add, coeff_X_pow_mul, F, coeff_mk,
    hshift, two_nsmul] at h
  omega

/-- Sum the three-step differences along the progression starting at `n`. -/
private theorem difference (n : ℕ) (hn : 9 < n) (k : ℕ) :
    (maxRookPartitionCount 3 (n + 3 * (k + 1)) : ℤ) - maxRookPartitionCount 3 n =
      ((k : ℤ) + 1) * (4 * (n : ℤ) - 9 + 6 * k) := by
  induction k with
  | zero => simpa using step n hn
  | succ k ih =>
    have hs := step (n + 3 * (k + 1)) (by omega)
    rw [Nat.mul_succ 3 (k + 1), ← Nat.add_assoc, Nat.cast_succ]
    push_cast at hs
    linear_combination hs + ih

end maxRookPartitionCount_three_modEq

/-- **Periodicity of $R_3(n)$ modulo $p$.** Let $R_3(n)$ be the number of partitions of $n$
with max-rook number $3$. For all natural numbers $p \ge 2$ and $n > 9$,
$R_3(n + 3p) \equiv R_3(n) \pmod{p}$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 6, second part
(`jis-2026-26.2.6-thm-6`). -/
public theorem maxRookPartitionCount_three_modEq (p n : ℕ) (hp : 2 ≤ p) (hn : 9 < n) :
    maxRookPartitionCount 3 (n + 3 * p) ≡ maxRookPartitionCount 3 n [MOD p] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd, Nat.cast_succ]
  exact ⟨_, maxRookPartitionCount_three_modEq.difference n hn k⟩

end MetaMathlibExt
