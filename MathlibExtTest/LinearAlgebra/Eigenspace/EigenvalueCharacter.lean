/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Eigenspace.EigenvalueCharacter

#check @Module.End.exists_algHom_of_forall_mem_span_singleton_of_mul_rev
#check @Module.End.exists_algHom_of_forall_mem_span_singleton

-- A common eigenvector of the generators is an eigenvector of every element.
example {F L A V : Type*} [Field F] [Field L] [Algebra F L] [Ring A] [Algebra F A]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] {X : Set A}
    (hX : Algebra.adjoin F X = ⊤) (δ : A →ₗ[F] Module.End L V) (h1 : δ 1 = 1)
    (hmul : ∀ a b : A, δ (a * b) = δ b * δ a) {v : V} (hv : v ≠ 0)
    (hX' : ∀ x ∈ X, ∃ c : L, δ x v = c • v) (a : A) : ∃ c : L, δ a v = c • v := by
  obtain ⟨χ, hχ, -⟩ :=
    Module.End.exists_algHom_of_forall_mem_span_singleton_of_mul_rev hX δ h1 hmul hv hX'
  exact ⟨χ a, hχ a⟩
