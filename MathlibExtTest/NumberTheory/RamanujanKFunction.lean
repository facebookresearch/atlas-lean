/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan
import MathlibExt.NumberTheory.RamanujanKFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

open MetaMathlibExt

example : ramanujanK 0 = 0 := ramanujanK_zero

-- The square of a nonreal point of the disk can lie on the negative real axis.
example :
    let X := ramanujanK (Complex.I / 2)
    let Y := ramanujanK (-1 / 4)
    (1 + Y) * X ^ 2 + 2 * Y * X = Y * (1 - Y) := by
  have h := ramanujanK_sq_relation (Complex.I / 2) (by norm_num [norm_div])
  rw [show (Complex.I / 2) ^ 2 = -1 / 4 by norm_num [div_pow, Complex.I_sq]] at h
  dsimp only
  linear_combination h

open MetaMathlibExt.QPochhammer

-- At x = 2 in this ring, x^32 vanishes, so factors whose exponents are at least
-- 32 can be omitted. This computes the cleared identity using only finite arithmetic.
private abbrev R := ZMod (2 ^ 32)

private def poch (r s : ℕ) (x : R) : R :=
  ((List.range 32).map fun n => 1 - x ^ (r + s * n)).prod

private def kNumerator (x : R) : R :=
  x * poch 1 10 x * poch 2 10 x * poch 8 10 x * poch 9 10 x

private def kDenominator (x : R) : R :=
  poch 3 10 x * poch 4 10 x * poch 6 10 x * poch 7 10 x

example :
    let x : R := 2
    (kNumerator x ^ 2 * kDenominator (x ^ 2) ^ 2 -
        kNumerator (x ^ 2) ^ 2 * kDenominator x ^ 2) * (x * poch 10 10 x ^ 4) =
      kNumerator x * kDenominator (x ^ 2) * kNumerator (x ^ 2) * kDenominator x *
        (poch 1 1 x * poch 5 5 x ^ 3) := by
  decide

-- Independently group a progression with leading exponent 3 and stride 2
-- into its three progressions with stride 6.
example : poch 3 2 (2 : R) = poch 3 6 2 * poch 5 6 2 * poch 7 6 2 := by decide

private def finiteTheta (a b : R) : R :=
  ((List.range 17).map fun i =>
    let n := (i : ℤ) - 8
    a ^ (n * (n + 1) / 2).toNat * b ^ (n * (n - 1) / 2).toNat).sum

private def finitePochhammer (a q : R) : R :=
  ((List.range 32).map fun n => 1 - a * q ^ n).prod

-- Compare the bilateral theta sum and the three products by computing them separately.
-- For these inputs terms outside [-8, 8] and factors beyond index 31 do not contribute.
example :
    let x : R := 2
    finiteTheta x (x ^ 2) =
      finitePochhammer (x ^ 3) (x ^ 3) * finitePochhammer (-x) (x ^ 3) *
        finitePochhammer (-x ^ 2) (x ^ 3) := by
  decide

-- At a zero base the first factor is the only one that can differ from one.
example : finitePochhammer 4 0 = -3 := by decide

-- Either theta parameter may be zero. The only surviving terms are at 0 and ±1.
example : finiteTheta 0 (4 : R) = 5 ∧ finiteTheta (4 : R) 0 = 5 := by decide

example : ramanujanThetaRaw 0 (1 / 2) = (3 / 2 : ℂ) := by
  rw [ramanujanThetaRaw_eq_qPochhammerInfRaw (a := 0) (b := 1 / 2) (by simp)]
  simp only [zero_mul, neg_zero, qPochhammerInfRaw_eq_tprod, sub_zero, tprod_one, one_mul]
  rw [tprod_eq_prod (s := {0})]
  · norm_num
  · intro n hn
    simp [zero_pow (by simpa using hn : n ≠ 0)]

-- The public complex identity also applies at a nonreal point of the disk.
example :
    ramanujanK (Complex.I / 2) / ramanujanK (-1 / 4) -
        ramanujanK (-1 / 4) / ramanujanK (Complex.I / 2) =
      qPochhammerInfRaw (Complex.I / 2) (Complex.I / 2) *
          qPochhammerInfRaw ((Complex.I / 2) ^ 5) ((Complex.I / 2) ^ 5) ^ 3 /
        ((Complex.I / 2) * qPochhammerInfRaw ((Complex.I / 2) ^ 10) ((Complex.I / 2) ^ 10) ^ 4) := by
  have h := ramanujanK_div_sub_div_sq (Complex.I / 2) (by norm_num [norm_div])
    (div_ne_zero Complex.I_ne_zero (by norm_num))
  rw [show (Complex.I / 2) ^ 2 = -1 / 4 by norm_num [div_pow, Complex.I_sq]] at h
  exact h
