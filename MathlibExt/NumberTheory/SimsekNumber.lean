/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace MetaMathlibExt

@[expose] public section

/-- Simsek numbers `y_1(n, k; lam)` in explicit finite-sum form:
    `(1 / k !) * ∑ j ∈ Finset.range (k + 1), C(k, j) * j ^ n * lam ^ j`.
    Source: equation (snmf1) of https://cs.uwaterloo.ca/journals/JIS/VOL26/Oussi/oussi9.tex;
    phrase concept `jis_term_8eae8e670c41baff4a5d1101`,
    semantic concept `jis_sem_cadb2d3c6cc457809c98725c`,
    source statement `jis_018cebafcc5d365ff500f619`. -/
public noncomputable def simsekNumber (n k : Nat) (lam : ℂ) : ℂ :=
  ((k.factorial : ℂ))⁻¹ *
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * (((j : ℂ) ^ n) * (lam ^ j))

/-- Defining finite-sum formula for `simsekNumber`. -/
public theorem simsekNumber_eq_sum (n k : Nat) (lam : ℂ) :
    simsekNumber n k lam =
      ((k.factorial : ℂ))⁻¹ *
        ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * (((j : ℂ) ^ n) * (lam ^ j)) :=
  rfl

/-- Boundary case `k = 0`: only the `j = 0` term survives. -/
public theorem simsekNumber_zero_k (n : Nat) (lam : ℂ) :
    simsekNumber n 0 lam = (0 : ℂ) ^ n := by
  unfold simsekNumber
  simp

/-- Boundary value at `n = 0` and `k = 0`. -/
public theorem simsekNumber_zero_zero (lam : ℂ) :
    simsekNumber 0 0 lam = 1 := by
  unfold simsekNumber
  simp

end

end MetaMathlibExt
