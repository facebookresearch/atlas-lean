/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Integer torsion in tensor products
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v w
open scoped TensorProduct
namespace TensorProduct
variable {R : Type u} [CommSemiring R]
  {M : Type v} [AddCommMonoid M] [Module R M]
  {N : Type w} [AddCommMonoid N] [Module R N]

/-- Torsion of the first actual factor kills every vector of the existing tensor product. -/
theorem nsmul_eq_zero_of_left (m : ℕ) (hM : ∀ x : M, m • x = 0) (x : M ⊗[R] N) :
    m • x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rw [smul_tmul', hM a, zero_tmul]
  | add a b ha hb => rw [nsmul_add, ha, hb, add_zero]

/-- Torsion of the second actual factor kills every vector of the existing tensor product. -/
theorem nsmul_eq_zero_of_right (m : ℕ) (hN : ∀ x : N, m • x = 0) (x : M ⊗[R] N) :
    m • x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rw [← tmul_smul, hN b, tmul_zero]
  | add a b ha hb => rw [nsmul_add, ha, hb, add_zero]

end TensorProduct
