/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Group.ForwardDiff

/-! # Recurrence for the floor-exponent binomial sums -/

namespace MetaMathlibExt

open Finset

/-- **Recurrence for the floor-exponent binomial sums.** Let $R$ be a commutative ring, $t \in R$
and $\ell \ge 1$ an integer, and for $m \ge 0$ let
$T_\ell(m; t) = \sum_{j=0}^{m} \binom{m}{j} t^{\lfloor j/\ell \rfloor}$. Then for every integer
$n \ge 0$,
$$\sum_{i=0}^{\ell} (-1)^i \binom{\ell}{i} T_\ell(n+\ell-i; t) - t\, T_\ell(n; t) = 0.$$

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 4.2 (`fq-2024-florez11012023-thm-4.2`). -/
public theorem floorPowBinomialSum_recurrence {R : Type*} [CommRing R] (t : R) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (n : ℕ) :
    ∑ i ∈ range (ℓ + 1), (ℓ.choose i : R) * (-1) ^ i *
        ∑ j ∈ range (n + ℓ - i + 1), ((n + ℓ - i).choose j : R) * t ^ (j / ℓ) -
      t * ∑ j ∈ range (n + 1), (n.choose j : R) * t ^ (j / ℓ) = 0 := by
  -- A forward difference shifts the weight in the binomial sum by one place.
  let B (k m : ℕ) := ∑ j ∈ range (m + 1), (m.choose j : R) * t ^ ((j + k) / ℓ)
  have step (k : ℕ) : fwdDiff 1 (B k) = B (k + 1) := by
    funext m
    apply sub_eq_iff_eq_add'.mpr
    simpa only [B, Nat.succ_add, Nat.add_succ] using
      sum_choose_succ_mul (fun j _ ↦ t ^ ((j + k) / ℓ)) m
  have iter (k : ℕ) : (fwdDiff (1 : ℕ))^[k] (B 0) = B k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, step]
  apply sub_eq_zero.mpr
  calc
    _ = (fwdDiff (1 : ℕ))^[ℓ] (B 0) n := by
      rw [fwdDiff_iter_eq_sum_shift, ← sum_range_reflect]
      refine sum_congr rfl fun i hi ↦ ?_
      have hiℓ : i ≤ ℓ := Nat.le_of_lt_succ (mem_range.mp hi)
      have hindex : n + ℓ - (ℓ - i) = n + i := by omega
      simp [B, hindex, Nat.choose_symm hiℓ, zsmul_eq_mul, mul_comm (ℓ.choose i : R)]
    _ = _ := by
      rw [iter, mul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [Nat.add_div_right j hℓ, pow_succ]
      ac_rfl

end MetaMathlibExt
