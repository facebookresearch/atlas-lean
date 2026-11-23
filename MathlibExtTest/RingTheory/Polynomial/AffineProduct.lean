/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import Mathlib.RingTheory.Polynomial.Vieta
public import MathlibExt.RingTheory.Polynomial.AffineProduct

open Polynomial

namespace Finset

/-! Source-specialized schemas over natural-number indices and integer
coefficients. -/

example (S : Finset ℕ) (r c : ℕ → ℤ) :
    ∏ s ∈ S, (C (r s) + X * C (c s)) =
      ∑ Q ∈ S.powerset, C (∏ s ∈ S, if s ∈ Q then c s else r s) * X ^ #Q :=
  prod_C_add_X_mul_C_eq_sum S r c

example (S : Finset ℕ) (r c : ℕ → ℤ) (i : ℕ) :
    (∏ s ∈ S, (C (r s) + X * C (c s))).coeff i =
      ∑ Q ∈ S.powersetCard i, ∏ s ∈ S, if s ∈ Q then c s else r s :=
  prod_C_add_X_mul_C_coeff S r c i

example (S : Finset ℕ) (r c : ℕ → ℤ) :
    (∏ s ∈ S, (C (r s) + X * C (c s))).natDegree ≤ #S :=
  prod_C_add_X_mul_C_natDegree_le S r c

example (S : Finset ℕ) (r c : ℕ → ℤ) (i : ℕ)
    (hr : ∀ s ∈ S, |r s| ≤ 1) (hc : ∀ s ∈ S, |c s| ≤ 1) :
    |(∏ s ∈ S, (C (r s) + X * C (c s))).coeff i| ≤
      ((#S).choose i : ℤ) :=
  abs_prod_C_add_X_mul_C_coeff_le_choose S r c i hr hc

/-! A populated asymmetric product has coefficients `-2`, `5`, and `12`. -/

private def asymmetricR (s : Fin 2) : ℤ := if s = 0 then 2 else -1

private def asymmetricC (s : Fin 2) : ℤ := if s = 0 then 3 else 4

example :
    (∏ s : Fin 2,
      (C (asymmetricR s) + X * C (asymmetricC s))).coeff 0 = -2 := by
  rw [prod_C_add_X_mul_C_coeff]
  decide

example :
    (∏ s : Fin 2, (C (asymmetricR s) + X * C (asymmetricC s))).coeff 1 = 5 := by
  rw [prod_C_add_X_mul_C_coeff]
  decide

example :
    (∏ s : Fin 2,
      (C (asymmetricR s) + X * C (asymmetricC s))).coeff 2 = 12 := by
  rw [prod_C_add_X_mul_C_coeff]
  decide

/-! The generalized identity also applies to a non-ring commutative semiring. -/

example :
    ∏ _s ∈ ({0} : Finset ℕ), (C (2 : ℕ) + X * C 3) =
      ∑ Q ∈ ({0} : Finset ℕ).powerset,
        C (∏ _s ∈ ({0} : Finset ℕ), if _s ∈ Q then 3 else 2) * X ^ #Q :=
  prod_C_add_X_mul_C_eq_sum _ _ _

/-! The two unit-bounded factors cancel in degree one. -/

example : (C (1 : ℤ) - X) * (C 1 + X) = 1 - X ^ 2 := by
  norm_num
  ring

example :
    (∏ b ∈ ({false, true} : Finset Bool),
      (C (1 : ℤ) + X * C (if b then 1 else -1))).coeff 1 = 0 := by
  rw [prod_C_add_X_mul_C_coeff]
  decide

example :
    |(∏ b ∈ ({false, true} : Finset Bool),
      (C (1 : ℤ) + X * C (if b then 1 else -1))).coeff 1| ≤
      (Nat.choose 2 1 : ℤ) := by
  apply abs_prod_C_add_X_mul_C_coeff_le_choose
  · simp
  · intro b _
    cases b <;> simp

/-! Empty, zero, and out-of-range coefficients. -/

example :
    (∏ _s ∈ (∅ : Finset ℕ), (C (7 : ℤ) + X * C 9)).coeff 0 = 1 := by
  rw [prod_C_add_X_mul_C_coeff]
  simp

example :
    (∏ _s ∈ (∅ : Finset ℕ), (C (7 : ℤ) + X * C 9)).coeff 1 = 0 := by
  rw [prod_C_add_X_mul_C_coeff]
  simp

example :
    (∏ _s ∈ ({0} : Finset ℕ), (C (0 : ℤ) + X * C 0)).coeff 0 = 0 := by
  rw [prod_C_add_X_mul_C_coeff]
  simp

example :
    (∏ _s ∈ ({0} : Finset ℕ), (C (2 : ℤ) + X * C 3)).coeff 2 = 0 := by
  rw [prod_C_add_X_mul_C_coeff]
  rw [powersetCard_eq_empty.2 (by decide)]
  simp

example :
    |(∏ _s ∈ ({0} : Finset ℕ),
      (C (1 : ℤ) + X * C 1)).coeff 2| ≤ (Nat.choose 1 2 : ℤ) := by
  apply abs_prod_C_add_X_mul_C_coeff_le_choose
  · simp
  · simp

/-! The affine formula specializes to Mathlib's canonical monic Vieta
formula. -/

example {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (S : Finset ι) (r : ι → R)
    (k : ℕ) (hk : k ≤ #S) :
    (∑ Q ∈ S.powersetCard k, ∏ s ∈ S, if s ∈ Q then 1 else r s) =
      ∑ Q ∈ S.powersetCard (#S - k), ∏ s ∈ Q, r s := by
  calc
    (∑ Q ∈ S.powersetCard k, ∏ s ∈ S, if s ∈ Q then 1 else r s) =
        (∏ s ∈ S, (C (r s) + X * C (1 : R))).coeff k :=
      (prod_C_add_X_mul_C_coeff S r (fun _ => 1) k).symm
    _ = ∑ Q ∈ S.powersetCard (#S - k), ∏ s ∈ Q, r s := by
      simpa [Polynomial.X_mul_C, add_comm] using prod_X_add_C_coeff S r hk

end Finset
