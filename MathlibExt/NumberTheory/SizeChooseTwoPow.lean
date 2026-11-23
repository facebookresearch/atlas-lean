/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Choose.Central

/-!
# Bit length of `Nat.choose (2 ^ n) (2 ^ (n - 1))`

For every `n ≥ 1` the binomial coefficient `Nat.choose (2 ^ n) (2 ^ (n - 1))` has exactly
`2 ^ n - n / 2` binary digits
(`MathlibExt.NumberTheory.OeisConjecturesWanted.size_choose_two_pow`).

## Proof outline

Write `N = 2 ^ (n - 1)` and `C = Nat.centralBinom N`, so that the binomial coefficient is
`Nat.choose (2 * N) N = C`. The recurrence
`(N + 1) * Nat.centralBinom (N + 1) = 2 * (2 * N + 1) * Nat.centralBinom N` gives, by induction
on `N`, the Wallis-type bounds `C ^ 2 * (2 * N + 1) ≤ 16 ^ N` and, for `N ≥ 1`,
`16 ^ N ≤ 4 * N * C ^ 2`. With `m = n / 2` we have `N ≤ 4 ^ m ≤ 2 * N`, hence
`(C * 2 ^ m) ^ 2 < C ^ 2 * (2 * N + 1) ≤ 16 ^ N ≤ 4 * N * C ^ 2 ≤ (C * 2 ^ (m + 1)) ^ 2`.
As `16 ^ N = (2 ^ (2 * N)) ^ 2`, taking square roots gives
`2 ^ (2 * N - m - 1) ≤ C < 2 ^ (2 * N - m)`, so `C` has `2 * N - m = 2 ^ n - n / 2` binary
digits.

## Implementation notes

`size_choose_two_pow` keeps the full name, the statement and the docstring it had as a wanted
theorem in `WantedExt.NumberTheory.OeisConjecturesWanted`, which imports this module. Its
hypothesis `1 ≤ n` follows the source; at `n = 0` the truncated subtraction `0 - 1 = 0` makes
both sides equal to `1`.

## References

The theorem's docstring cites its source, Sela Fried's *Proofs of Several Conjectures From the
OEIS* (Journal of Integer Sequences 28 (2025), Article 25.4.3). The same author's arXiv preprint
*Proofs of some Conjectures from the OEIS* (arXiv:2410.07237v3) proves the result as its
Theorem 1, notes that it was conjectured in OEIS A112884, and estimates the binary logarithm of
the binomial coefficient with the Euler–Maclaurin formula. The proof here uses the elementary
bounds above instead.
-/

namespace MathlibExt.NumberTheory.OeisConjecturesWanted

/-- The upper Wallis-type bound `centralBinom N ^ 2 * (2 * N + 1) ≤ 16 ^ N`. -/
private theorem centralBinom_sq_mul_le (N : ℕ) :
    N.centralBinom ^ 2 * (2 * N + 1) ≤ 16 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h := Nat.succ_mul_centralBinom_succ N
    have key : (N + 1) ^ 2 * ((N + 1).centralBinom ^ 2 * (2 * (N + 1) + 1)) ≤
        (N + 1) ^ 2 * 16 ^ (N + 1) := by
      calc (N + 1) ^ 2 * ((N + 1).centralBinom ^ 2 * (2 * (N + 1) + 1))
          = ((N + 1) * (N + 1).centralBinom) ^ 2 * (2 * N + 3) := by ring
        _ = 4 * ((2 * N + 1) * (2 * N + 3)) * (N.centralBinom ^ 2 * (2 * N + 1)) := by
          rw [h]; ring
        _ ≤ 4 * ((2 * N + 1) * (2 * N + 3)) * 16 ^ N := Nat.mul_le_mul_left _ ih
        _ ≤ 16 * (N + 1) ^ 2 * 16 ^ N := Nat.mul_le_mul_right _ (by nlinarith)
        _ = (N + 1) ^ 2 * 16 ^ (N + 1) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- The lower Wallis-type bound `16 ^ N ≤ 4 * N * centralBinom N ^ 2` for `N ≥ 1`. -/
private theorem sixteen_pow_le_mul_centralBinom_sq {N : ℕ} (hN : 1 ≤ N) :
    16 ^ N ≤ 4 * N * N.centralBinom ^ 2 := by
  induction N, hN using Nat.le_induction with
  | base => decide
  | succ N hN ih =>
    have h := Nat.succ_mul_centralBinom_succ N
    have key : (N + 1) ^ 2 * 16 ^ (N + 1) ≤
        (N + 1) ^ 2 * (4 * (N + 1) * (N + 1).centralBinom ^ 2) := by
      calc (N + 1) ^ 2 * 16 ^ (N + 1) = 16 * (N + 1) ^ 2 * 16 ^ N := by ring
        _ ≤ 16 * (N + 1) ^ 2 * (4 * N * N.centralBinom ^ 2) := Nat.mul_le_mul_left _ ih
        _ = 16 * (N + 1) * N.centralBinom ^ 2 * (4 * N * (N + 1)) := by ring
        _ ≤ 16 * (N + 1) * N.centralBinom ^ 2 * (2 * N + 1) ^ 2 :=
          Nat.mul_le_mul_left _ (by nlinarith)
        _ = 4 * (N + 1) * ((N + 1) * (N + 1).centralBinom) ^ 2 := by rw [h]; ring
        _ = (N + 1) ^ 2 * (4 * (N + 1) * (N + 1).centralBinom ^ 2) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- **Bit length of $\binom{2^n}{2^{n-1}}$.** For every integer $n \ge 1$, the binary expansion of
the binomial coefficient $\binom{2^n}{2^{n-1}}$ has exactly $2^n - \lfloor n/2 \rfloor$ digits.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Theorem 6. -/
public theorem size_choose_two_pow (n : ℕ) (hn : 1 ≤ n) :
    Nat.size (Nat.choose (2 ^ n) (2 ^ (n - 1))) =
      2 ^ n - n / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h2n : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
  rw [Nat.add_sub_cancel, h2n, ← Nat.centralBinom_eq_two_mul_choose]
  set N := 2 ^ k with hN
  set m := (k + 1) / 2 with hm
  set c := N.centralBinom
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  -- `N = 2 ^ k ≤ 4 ^ m ≤ 2 ^ (k + 1) = 2 * N`, since `k ≤ 2 * m ≤ k + 1`.
  have h4m : 4 ^ m ≤ 2 * N := by
    rw [← h2n, h4, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN4m : N ≤ 4 ^ m := by
    rw [hN, h4, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hNpos : 1 ≤ N := Nat.one_le_two_pow
  have hmN : m + 1 ≤ 2 * N := by
    have := Nat.lt_pow_self (n := m) (show 1 < 4 by norm_num)
    omega
  have h16 : 16 ^ N = (2 ^ (2 * N)) ^ 2 := by
    rw [← pow_mul, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    ring_nf
  apply le_antisymm
  · -- `c < 2 ^ (2 * N - m)`, from `(c * 2 ^ m) ^ 2 < (2 ^ (2 * N)) ^ 2`.
    rw [Nat.size_le]
    have hsq : (c * 2 ^ m) ^ 2 < (2 ^ (2 * N)) ^ 2 := by
      calc (c * 2 ^ m) ^ 2 = c ^ 2 * 4 ^ m := by
            rw [mul_pow, ← pow_mul, h4, ← pow_mul, mul_comm m 2]
        _ < c ^ 2 * (2 * N + 1) :=
          Nat.mul_lt_mul_of_pos_left (by omega) (pow_pos (Nat.centralBinom_pos N) 2)
        _ ≤ 16 ^ N := centralBinom_sq_mul_le N
        _ = (2 ^ (2 * N)) ^ 2 := h16
    have hlt : c * 2 ^ m < 2 ^ (2 * N - m) * 2 ^ m := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
    exact Nat.lt_of_mul_lt_mul_right hlt
  · -- `2 ^ (2 * N - m - 1) ≤ c`, from `(2 ^ (2 * N)) ^ 2 ≤ (c * 2 ^ (m + 1)) ^ 2`.
    have hsq : (2 ^ (2 * N)) ^ 2 ≤ (c * 2 ^ (m + 1)) ^ 2 := by
      calc (2 ^ (2 * N)) ^ 2 = 16 ^ N := h16.symm
        _ ≤ 4 * N * c ^ 2 := sixteen_pow_le_mul_centralBinom_sq hNpos
        _ ≤ 4 * 4 ^ m * c ^ 2 := by gcongr
        _ = (c * 2 ^ (m + 1)) ^ 2 := by
          rw [mul_pow, ← pow_mul, h4, ← pow_mul, ← pow_add]
          ring_nf
    have hle : 2 ^ (2 * N - m - 1) * 2 ^ (m + 1) ≤ c * 2 ^ (m + 1) := by
      rw [← pow_add, show 2 * N - m - 1 + (m + 1) = 2 * N by omega]
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsq
    have hpow := Nat.le_of_mul_le_mul_right hle (by positivity)
    have hsize : 2 * N - m - 1 < Nat.size c := Nat.lt_size.2 hpow
    omega

end MathlibExt.NumberTheory.OeisConjecturesWanted
