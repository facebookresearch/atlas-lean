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
# Natural-number torsion passes to tensor products

Let R be a commutative semiring and M,N R-semimodules. If multiplication by a natural number m
annihilates either whole factor, it annihilates every vector of M⊗_RN.
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

/-- **Torsion of the first factor annihilates the tensor.**

Let R be a commutative semiring, M,N R-semimodules and m∈ℕ. If m•x=0 for all x∈M, then m•z=0
for all z∈M⊗_RN.
-/
theorem nsmul_eq_zero_of_left (m : ℕ) (hM : ∀ x : M, m • x = 0) (x : M ⊗[R] N) :
    m • x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rw [smul_tmul', hM a, zero_tmul]
  | add a b ha hb => rw [nsmul_add, ha, hb, add_zero]

/-- **Torsion of the second factor annihilates the tensor.**

Let R be a commutative semiring, M,N R-semimodules and m∈ℕ. If m•y=0 for all y∈N, then m•z=0
for all z∈M⊗_RN.
-/
theorem nsmul_eq_zero_of_right (m : ℕ) (hN : ∀ x : N, m • x = 0) (x : M ⊗[R] N) :
    m • x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rw [← tmul_smul, hN b, tmul_zero]
  | add a b ha hb => rw [nsmul_add, ha, hb, add_zero]

end TensorProduct
