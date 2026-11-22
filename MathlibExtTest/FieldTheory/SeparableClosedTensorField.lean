/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic
public import MathlibExt.FieldTheory.SeparableClosedTensorField

@[expose] public section

open scoped TensorProduct

universe u v w

/-- Consumer with the original binders, universe-polymorphic in `u, v, w`. -/
example (k : Type u) (F : Type v) (K : Type w) [Field k] [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra.IsSeparable k K]
    (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range) :
    IsField (F ⊗[k] K) :=
  Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range k F K hsc

/-- Higher-universe consumer: fields in `Type 1`, `Type 2`, and `Type 3`. -/
example (k : Type 1) (F : Type 2) (K : Type 3) [Field k] [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra.IsSeparable k K]
    (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range) :
    IsField (F ⊗[k] K) :=
  Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range k F K hsc

/-- Boundary: when `F = k`, the separable-closedness hypothesis holds
trivially, so the tensor product is a field for separable `K / k`. -/
example (k : Type u) (K : Type w) [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K] : IsField (k ⊗[k] K) :=
  Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range k k K
    (fun y _ => ⟨y, by simp⟩)
