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

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Finite pure expressions in balanced tensor quotients

Lifting through the quotient and applying the tensor finite-sum lemma gives
finite sums of ordered pure factors.
-/

@[expose] public section

open scoped TensorProduct

universe u v w z

namespace TensorProduct.Balanced

variable (k : Type u) (R : Type v) (M : Type w) (N : Type z)
  [CommRing k] [Semiring R] [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module Rᵐᵒᵖ M] [Module R N]

/-- Every actual balanced class is a finite sum of its ordered pure classes. -/
theorem exists_finset (x : TensorProduct.Balanced k R M N) :
    ∃ s : Finset (M × N), x = ∑ a ∈ s, mk k R M N a.1 a.2 := by
  classical
  obtain ⟨z, rfl⟩ := (balanceRelations k R M N).mkQ_surjective x
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset z
  refine ⟨s, ?_⟩
  change (balanceRelations k R M N).mkQ z =
    ∑ a ∈ s, (balanceRelations k R M N).mkQ (a.1 ⊗ₜ[k] a.2)
  rw [hs, map_sum]

end TensorProduct.Balanced
