/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.MixedComplex.ConnesFunctoriality
public import MathlibExt.Algebra.Homology.PartialTotalSignedRowHomology

/-!
# The full column signs of the printed Loday BC convention

The column sign c_p has triangular exponent p(p-1)/2. Combined with the
native signed-row component epsilon(p)^q it gives the actual cell coordinate
sign. Its vertical difference is epsilon(p), and its horizontal difference
is (-1)^(q+p), hence (-1)^(n+1) on a horizontal arrow out of C_n.
These are full column/entry changes of coordinates, not a replacement of the
mixed operator alone while its chain differential stays fixed.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive

namespace MixedComplex

/-- The actual triangular column-sign sequence c_(p+1)=c_p*(-1)^p. -/
def lodayColumnSign : ℕ → ℤˣ
  | 0 => 1
  | p + 1 => lodayColumnSign p * (-1 : ℤˣ) ^ p

@[simp]
theorem lodayColumnSign_zero : lodayColumnSign 0 = 1 := rfl

@[simp]
theorem lodayColumnSign_succ (p : ℕ) :
    lodayColumnSign (p + 1) = lodayColumnSign p * (-1 : ℤˣ) ^ p := rfl

private theorem negOnePow_square (p : ℕ) : (-1 : ℤˣ) ^ p * (-1 : ℤˣ) ^ p = 1 := by
  rw [← pow_add]
  exact (show Even (p + p) from ⟨p, rfl⟩).neg_one_pow

/-- Every original column coordinate sign is an involution. -/
theorem lodayColumnSign_square (p : ℕ) : lodayColumnSign p * lodayColumnSign p = 1 := by
  induction p with
  | zero => simp only [lodayColumnSign_zero, one_mul]
  | succ p ih =>
    rw [lodayColumnSign_succ, mul_mul_mul_comm, ih, negOnePow_square, one_mul]

/-- Inverse column coordinates are the same original signs. -/
theorem lodayColumnSign_inv (p : ℕ) : (lodayColumnSign p)⁻¹ = lodayColumnSign p := by
  apply (mul_left_cancel (a := lodayColumnSign p))
  rw [mul_inv_cancel, lodayColumnSign_square]

/-- Adjacent column signs differ by the native outer epsilon factor. -/
theorem lodayColumnSign_succ_mul (p : ℕ) :
    lodayColumnSign (p + 1) * lodayColumnSign p = (-1 : ℤˣ) ^ p := by
  rw [lodayColumnSign_succ, mul_assoc, mul_comm ((-1 : ℤˣ) ^ p), ← mul_assoc,
    lodayColumnSign_square, one_mul]

/-- The actual entry coordinate sign c_p*epsilon(p)^q. -/
def lodayCellSign (p q : ℕ) : ℤˣ := lodayColumnSign p * ((ComplexShape.down ℕ).ε p) ^ q

/-- Entry coordinate signs are involutions. -/
theorem lodayCellSign_square (p q : ℕ) : lodayCellSign p q * lodayCellSign p q = 1 := by
  rw [lodayCellSign, mul_mul_mul_comm, lodayColumnSign_square]
  simp only [ComplexShape.ε_down_ℕ, ← pow_mul]
  rw [negOnePow_square, one_mul]

/-- The vertical entry-sign difference exactly removes the canonical stored column sign. -/
theorem lodayCellSign_vertical (p q : ℕ) :
    lodayCellSign p (q + 1) * lodayCellSign p q = (ComplexShape.down ℕ).ε p := by
  rw [lodayCellSign, lodayCellSign, mul_mul_mul_comm, lodayColumnSign_square, one_mul,
    pow_succ, mul_assoc]
  have he : ((ComplexShape.down ℕ).ε p) ^ q * ((ComplexShape.down ℕ).ε p) ^ q = 1 := by
    rw [ComplexShape.ε_down_ℕ, ← pow_mul]
    exact negOnePow_square (p * q)
  rw [mul_comm ((ComplexShape.down ℕ).ε p) (((ComplexShape.down ℕ).ε p) ^ q),
    ← mul_assoc, he, one_mul]

/-- The horizontal entry-sign difference is the original printed degree sign. -/
theorem lodayCellSign_horizontal (p q : ℕ) :
    lodayCellSign (p + 1) q * lodayCellSign p q = (-1 : ℤˣ) ^ (p + q) := by
  rw [lodayCellSign, lodayCellSign, mul_mul_mul_comm, lodayColumnSign_succ_mul,
    ← mul_pow, ComplexShape.ε_down_ℕ, ComplexShape.ε_down_ℕ]
  have h : (-1 : ℤˣ) ^ (p + 1) * (-1 : ℤˣ) ^ p = -1 := by
    rw [← pow_add]
    exact (show Odd (p + 1 + p) from ⟨p, by omega⟩).neg_one_pow
  rw [h, ← pow_add]

/-- A horizontal arrow at underlying source degree n has exactly the printed (-1)^(n+1) factor. -/
theorem lodayCellSign_horizontal_degree (p n : ℕ) :
    lodayCellSign (p + 1) (n + p + 1) * lodayCellSign p (n + p + 1) =
      (-1 : ℤˣ) ^ (n + 1) := by
  rw [lodayCellSign_horizontal]
  rw [show p + (n + p + 1) = (p + p) + (n + 1) by omega, pow_add,
    (show Even (p + p) from ⟨p, rfl⟩).neg_one_pow, one_mul]

end MixedComplex
