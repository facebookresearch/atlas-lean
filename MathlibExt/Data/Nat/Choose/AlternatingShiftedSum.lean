/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.ForwardDiff

/-! # Alternating sum of shifted binomial coefficients -/

namespace MetaMathlibExt

open Finset

set_option linter.unusedVariables false in
/-- **Alternating sum of shifted binomial coefficients.** Let $\ell$, $n$, $j$ and $s$ be natural
numbers with $1 \le \ell \le n$, $j \ge 1$ and $\ell j + s \le n$. Then
$$\sum_{i=0}^{\ell} (-1)^i \binom{\ell}{i} \binom{n-i}{\ell j+s} = \binom{n-\ell}{\ell(j-1)+s}.$$

The paper states this for $\lfloor (1-s)/\ell \rfloor \le j \le \lfloor (n-s)/\ell \rfloor$; only
$j \ge 1$ is stated here, since for $j \le 0$ the right side can have a negative lower index. For
$j \ge 1$ the bound $j \le \lfloor (n-s)/\ell \rfloor$ is the condition $\ell j + s \le n$.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 4.1 (`fq-2024-florez11012023-lem-4.1`). -/
public theorem alternating_sum_choose_mul_choose_sub {ℓ n j s : ℕ} (hℓ : 1 ≤ ℓ)
    (hℓn : ℓ ≤ n) (hj : 1 ≤ j) (hjn : ℓ * j + s ≤ n) :
    ∑ i ∈ range (ℓ + 1), (ℓ.choose i : ℤ) * (-1) ^ i * ((n - i).choose (ℓ * j + s) : ℤ) =
      ((n - ℓ).choose (ℓ * (j - 1) + s) : ℤ) := by
  have hindex : ℓ + (ℓ * (j - 1) + s) = ℓ * j + s := by
    rw [← Nat.add_assoc, Nat.add_comm ℓ, ← Nat.mul_add_one, Nat.sub_add_cancel hj]
  -- Expand the forward difference at n - ℓ, then reverse the summation order.
  have h := congrFun (fwdDiff_iter_choose (R := ℤ) (ℓ * (j - 1) + s) ℓ) (n - ℓ)
  rw [fwdDiff_iter_eq_sum_shift] at h
  rw [← sum_range_reflect]
  refine (sum_congr rfl ?_).trans h
  intro i hi
  have hiℓ : i ≤ ℓ := Nat.le_of_lt_succ (mem_range.mp hi)
  simp only [Nat.add_sub_cancel, Nat.choose_symm hiℓ, hindex, smul_eq_mul, mul_one]
  rw [show n - (ℓ - i) = n - ℓ + i by omega, mul_comm (ℓ.choose i : ℤ)]

end MetaMathlibExt
