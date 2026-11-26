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
# Column and cell signs for BC mixed-complex coordinates

The column units are c₀=1 and c_{p+1}=c_p(-1)^p, equivalently c_p=(-1)^{p(p-1)/2}. Each is an
involution. In a down–down bicomplex the outer sign is ε_p=(-1)^p, giving the cell coordinate
s_{p,q}=c_p ε_p^q.

The vertical ratio is s_{p,q+1}s_{p,q}=ε_p. The horizontal ratio is s_{p+1,q}s_{p,q}=(-1)^{p+q}.
At a horizontal arrow from underlying mixed degree n, q=n+p+1, so this ratio is (-1)^{n+1}.
These signs describe full column and cell coordinate changes.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive

namespace MixedComplex

/-- For p∈ℕ, define the integer unit c_p recursively by c₀=1 and c_{p+1}=c_p(-1)^p. Its triangular
exponent is p(p-1)/2, so c_p=(-1)^{p(p-1)/2}. -/
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

/-- For the integer units c₀=1,c_{p+1}=c_p(-1)^p and any p∈ℕ, c_p c_p=1. Thus each column sign is an
involution. -/
theorem lodayColumnSign_square (p : ℕ) : lodayColumnSign p * lodayColumnSign p = 1 := by
  induction p with
  | zero => simp only [lodayColumnSign_zero, one_mul]
  | succ p ih =>
    rw [lodayColumnSign_succ, mul_mul_mul_comm, ih, negOnePow_square, one_mul]

/-- For p∈ℕ and the triangular unit c_p, c_p⁻¹=c_p. This follows from c_p²=1. -/
theorem lodayColumnSign_inv (p : ℕ) : (lodayColumnSign p)⁻¹ = lodayColumnSign p := by
  apply (mul_left_cancel (a := lodayColumnSign p))
  rw [mul_inv_cancel, lodayColumnSign_square]

/-- For p∈ℕ, c_{p+1}c_p=(-1)^p as integer units, where c₀=1 and c_{p+1}=c_p(-1)^p. -/
theorem lodayColumnSign_succ_mul (p : ℕ) :
    lodayColumnSign (p + 1) * lodayColumnSign p = (-1 : ℤˣ) ^ p := by
  rw [lodayColumnSign_succ, mul_assoc, mul_comm ((-1 : ℤˣ) ^ p), ← mul_assoc,
    lodayColumnSign_square, one_mul]

/-- For p,q∈ℕ, the cell unit is s_{p,q}=c_p ε_p^q=c_p(-1)^{pq}, with ε_p=(-1)^p for the outer down
shape and c_p the triangular column sign. -/
def lodayCellSign (p q : ℕ) : ℤˣ := lodayColumnSign p * ((ComplexShape.down ℕ).ε p) ^ q

/-- For p,q∈ℕ and s_{p,q}=c_p(-1)^{pq}, one has s_{p,q}s_{p,q}=1 in the integer units. -/
theorem lodayCellSign_square (p q : ℕ) : lodayCellSign p q * lodayCellSign p q = 1 := by
  rw [lodayCellSign, mul_mul_mul_comm, lodayColumnSign_square]
  simp only [ComplexShape.ε_down_ℕ, ← pow_mul]
  rw [negOnePow_square, one_mul]

/-- For p,q∈ℕ, s_{p,q+1}s_{p,q}=ε_p=(-1)^p. This ratio removes the sign of the canonical stored
column differential. -/
theorem lodayCellSign_vertical (p q : ℕ) :
    lodayCellSign p (q + 1) * lodayCellSign p q = (ComplexShape.down ℕ).ε p := by
  rw [lodayCellSign, lodayCellSign, mul_mul_mul_comm, lodayColumnSign_square, one_mul,
    pow_succ, mul_assoc]
  have he : ((ComplexShape.down ℕ).ε p) ^ q * ((ComplexShape.down ℕ).ε p) ^ q = 1 := by
    rw [ComplexShape.ε_down_ℕ, ← pow_mul]
    exact negOnePow_square (p * q)
  rw [mul_comm ((ComplexShape.down ℕ).ε p) (((ComplexShape.down ℕ).ε p) ^ q),
    ← mul_assoc, he, one_mul]

/-- For p,q∈ℕ, s_{p+1,q}s_{p,q}=(-1)^{p+q}. The units c_p are triangular and the remaining factor is
the signed-row parity. -/
theorem lodayCellSign_horizontal (p q : ℕ) :
    lodayCellSign (p + 1) q * lodayCellSign p q = (-1 : ℤˣ) ^ (p + q) := by
  rw [lodayCellSign, lodayCellSign, mul_mul_mul_comm, lodayColumnSign_succ_mul,
    ← mul_pow, ComplexShape.ε_down_ℕ, ComplexShape.ε_down_ℕ]
  have h : (-1 : ℤˣ) ^ (p + 1) * (-1 : ℤˣ) ^ p = -1 := by
    rw [← pow_add]
    exact (show Odd (p + 1 + p) from ⟨p, by omega⟩).neg_one_pow
  rw [h, ← pow_add]

/-- For p,n∈ℕ set q=n+p+1. Then s_{p+1,q}s_{p,q}=(-1)^{n+1}. The source cell (p+1,q) has underlying
mixed degree q-(p+1)=n, and its target (p,q) has degree n+1. -/
theorem lodayCellSign_horizontal_degree (p n : ℕ) :
    lodayCellSign (p + 1) (n + p + 1) * lodayCellSign p (n + p + 1) =
      (-1 : ℤˣ) ^ (n + 1) := by
  rw [lodayCellSign_horizontal]
  rw [show p + (n + p + 1) = (p + p) + (n + 1) by omega, pow_add,
    (show Even (p + p) from ⟨p, rfl⟩).neg_one_pow, one_mul]

end MixedComplex
