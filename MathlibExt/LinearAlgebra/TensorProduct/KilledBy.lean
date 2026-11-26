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
# Natural-number annihilation in semimodule tensor products

Let R be a commutative semiring and M,N semimodules with additive commutative monoid structures,
in independent universes. If a natural number m annihilates every element of M by repeated
addition, it annihilates every element of M⊗_R N. The same holds when it annihilates N.

On pure tensors, natural-number multiplication can be moved to either factor. Additivity extends
the vanishing to the whole tensor product. The statements include m=0 and require no additive
inverses.
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

/-- Let R be a commutative semiring, M,N additive commutative monoid semimodules in independent
carrier universes, and m∈ℕ. If m•a=0 for every a∈M, then m•x=0 for every x∈M⊗_R N. On a pure
tensor, m•(a⊗b)=(m•a)⊗b. -/
theorem nsmul_eq_zero_of_left (m : ℕ) (hM : ∀ x : M, m • x = 0) (x : M ⊗[R] N) :
    m • x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rw [smul_tmul', hM a, zero_tmul]
  | add a b ha hb => rw [nsmul_add, ha, hb, add_zero]

/-- Let R be a commutative semiring and M,N additive commutative monoid semimodules, with
independent scalar and carrier universes. For m∈ℕ, if m•b=0 for all b∈N then m•x=0 for every
x∈M⊗_R N. The balanced tensor relation moves repeated addition to the right factor. -/
theorem nsmul_eq_zero_of_right (m : ℕ) (hN : ∀ x : N, m • x = 0) (x : M ⊗[R] N) :
    m • x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rw [← tmul_smul, hN b, tmul_zero]
  | add a b ha hb => rw [nsmul_add, ha, hb, add_zero]

end TensorProduct
