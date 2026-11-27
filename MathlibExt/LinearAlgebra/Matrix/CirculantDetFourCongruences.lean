/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.LinearAlgebra.Matrix.CirculantDetFour
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.LinearCombination

/-!
# Congruences for the four-by-four circulant determinant

The factorization of the determinant gives its residue modulo 16 for two patterns of odd entries.
-/

namespace MetaMathlibExt

/-- **The 4 × 4 circulant determinant modulo 16 at two parity patterns.** For all integers
$k$, $l$, $m$, $n$, the $4 \times 4$ circulant determinant $D_4$ satisfies
$D_4(2k + 1, 2l, 2m, 2n) \equiv 8m + 1 \pmod{16}$ and
$D_4(2k, 2l + 1, 2m + 1, 2n + 1) \equiv 8(k + l + n) - 3 \pmod{16}$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 6 (`integers-2024-A30-lem-6`). -/
public theorem circulantDetFour_mod_sixteen (k l m n : ℤ) :
    circulantDetFour ![2 * k + 1, 2 * l, 2 * m, 2 * n] ≡ 8 * m + 1 [ZMOD 16] ∧
      circulantDetFour ![2 * k, 2 * l + 1, 2 * m + 1, 2 * n + 1] ≡
        8 * (k + l + n) - 3 [ZMOD 16] := by
  constructor <;> rw [circulantDetFour_eq, Int.modEq_iff_dvd]
  -- The factors are `1 + 4 * a` and `1 + 4 * b` in both cases. Their product contains
  -- `16 * a * b`; the remaining difference uses even products of consecutive integers.
  · let a := (k + m) * (k + m + 1) - (l + n) ^ 2
    let b := (k - m) * (k - m + 1) + (l - n) ^ 2
    obtain ⟨r, hr⟩ := Int.even_mul_succ_self k
    obtain ⟨s, hs⟩ := Int.even_mul_pred_self m
    refine ⟨l * n - a * b - r - s, ?_⟩
    dsimp [a, b]
    linear_combination -8 * hr - 8 * hs
  · let a := (k + m) * (k + m + 1) - (l + n + 1) ^ 2
    let b := (k - m - 1) * (k - m) + (l - n) ^ 2
    obtain ⟨r, hr⟩ := Int.even_mul_pred_self k
    obtain ⟨s, hs⟩ := Int.even_mul_succ_self m
    refine ⟨l * n + l + n - a * b - r - s, ?_⟩
    dsimp [a, b]
    linear_combination -8 * hr - 8 * hs

end MetaMathlibExt
