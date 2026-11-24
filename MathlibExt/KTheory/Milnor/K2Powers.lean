/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.K2

/-!
# Power laws for binary K₂ symbols

Powers in each slot of the binary symbol scale by `nsmul`/`zsmul`.
-/

@[expose] public section

namespace MilnorK
namespace MilnorKRing

variable {F : Type*} [Field F]

/-- Natural power in the left slot scales by `nsmul`. -/
theorem k2Symbol_pow_left (a b : Fˣ) (n : ℕ) :
    k2Symbol (F := F) (a ^ n) b = n • k2Symbol a b := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    calc
      k2Symbol (a ^ (n + 1)) b = k2Symbol (a ^ n * a) b := by rw [pow_succ]
      _ = k2Symbol (a ^ n) b + k2Symbol a b := k2Symbol_mul_left _ _ _
      _ = n • k2Symbol a b + k2Symbol a b := by rw [ih]
      _ = (n + 1) • k2Symbol a b := by rw [← AddMonoid.nsmul_succ]

/-- Natural power in the right slot scales by `nsmul`. -/
theorem k2Symbol_pow_right (a b : Fˣ) (n : ℕ) :
    k2Symbol (F := F) a (b ^ n) = n • k2Symbol a b := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    calc
      k2Symbol a (b ^ (n + 1)) = k2Symbol a (b ^ n * b) := by rw [pow_succ]
      _ = k2Symbol a (b ^ n) + k2Symbol a b := k2Symbol_mul_right _ _ _
      _ = n • k2Symbol a b + k2Symbol a b := by rw [ih]
      _ = (n + 1) • k2Symbol a b := by rw [← AddMonoid.nsmul_succ]

/-- Integer power in the left slot scales by `zsmul`. -/
theorem k2Symbol_zpow_left (a b : Fˣ) (n : ℤ) :
    k2Symbol (F := F) (a ^ n) b = n • k2Symbol a b := by
  cases n with
  | ofNat m =>
    calc
      k2Symbol (a ^ (Int.ofNat m)) b = k2Symbol (a ^ m) b := by rfl
      _ = m • k2Symbol a b := k2Symbol_pow_left a b m
      _ = (Int.ofNat m) • k2Symbol a b := by rfl
  | negSucc m =>
    calc
      k2Symbol (a ^ (Int.negSucc m)) b = k2Symbol ((a ^ (m + 1))⁻¹) b := by rfl
      _ = - k2Symbol (a ^ (m + 1)) b := k2Symbol_inv_left _ _
      _ = - ((m + 1) • k2Symbol a b) := by rw [k2Symbol_pow_left]
      _ = - (((m + 1 : ℕ) : ℤ) • k2Symbol a b) := by simp
      _ = (- ((m + 1 : ℕ) : ℤ)) • k2Symbol a b :=
        Eq.symm (neg_zsmul (k2Symbol (F := F) a b) ↑(m + 1))
      _ = (Int.negSucc m) • k2Symbol a b := by simp [Int.negSucc_eq]

/-- Integer power in the right slot scales by `zsmul`. -/
theorem k2Symbol_zpow_right (a b : Fˣ) (n : ℤ) :
    k2Symbol (F := F) a (b ^ n) = n • k2Symbol a b := by
  cases n with
  | ofNat m =>
    calc
      k2Symbol a (b ^ (Int.ofNat m)) = k2Symbol a (b ^ m) := by rfl
      _ = m • k2Symbol a b := k2Symbol_pow_right a b m
      _ = (Int.ofNat m) • k2Symbol a b := by rfl
  | negSucc m =>
    calc
      k2Symbol a (b ^ (Int.negSucc m)) = k2Symbol a ((b ^ (m + 1))⁻¹) := by rfl
      _ = - k2Symbol a (b ^ (m + 1)) := k2Symbol_inv_right _ _
      _ = - ((m + 1) • k2Symbol a b) := by rw [k2Symbol_pow_right]
      _ = - (((m + 1 : ℕ) : ℤ) • k2Symbol a b) := by simp
      _ = (- ((m + 1 : ℕ) : ℤ)) • k2Symbol a b :=
        Eq.symm (neg_zsmul (k2Symbol (F := F) a b) ↑(m + 1))
      _ = (Int.negSucc m) • k2Symbol a b := by simp [Int.negSucc_eq]

/-- Natural powers in both slots give the product scalar `(m * n)`. -/
theorem k2Symbol_pow_pow (a b : Fˣ) (m n : ℕ) :
    k2Symbol (F := F) (a ^ m) (b ^ n) = (m * n) • k2Symbol a b := by
  calc
    k2Symbol (a ^ m) (b ^ n) = m • k2Symbol a (b ^ n) := k2Symbol_pow_left _ _ _
    _ = m • (n • k2Symbol a b) := by rw [k2Symbol_pow_right]
    _ = (m * n) • k2Symbol a b := by rw [smul_smul]

/-- Integer powers in both slots give the product scalar `(m * n)` for `zsmul`. -/
theorem k2Symbol_zpow_zpow (a b : Fˣ) (m n : ℤ) :
    k2Symbol (F := F) (a ^ m) (b ^ n) = (m * n) • k2Symbol a b := by
  calc
    k2Symbol (a ^ m) (b ^ n) = m • k2Symbol a (b ^ n) := k2Symbol_zpow_left _ _ _
    _ = m • (n • k2Symbol a b) := by rw [k2Symbol_zpow_right]
    _ = (m * n) • k2Symbol a b := by rw [smul_smul]

end MilnorKRing
end MilnorK
