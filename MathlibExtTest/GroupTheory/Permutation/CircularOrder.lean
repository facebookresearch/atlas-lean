/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from `fairinternal/formal-math/MathlibExtTest/GroupTheory/Permutation/CircularOrder.lean`
at commit `5edfb3b6f668f04b907ff6ca3a98cb0ce1c2eb64`.
Original source SHA-256: a1ee7f830e5f7f2fcc5fc3624e0f7b3b57eef3bbc09f64f2b2495fa5fe004249
-/

module

public import MathlibExt.GroupTheory.Permutation.CircularOrder

@[expose] public section

example (α : Type*) [CircularOrder α] (σ : Equiv.Perm α) :
    σ ∈ MetaMathlibExt.circularOrderAutSubgroup α ↔
      ∀ a b c, btw a b c ↔ btw (σ a) (σ b) (σ c) :=
  MetaMathlibExt.mem_circularOrderAutSubgroup σ

example (α : Type*) [CircularOrder α] :
    (1 : Equiv.Perm α) ∈ MetaMathlibExt.circularOrderAutSubgroup α :=
  Subgroup.one_mem _

example (α : Type*) [CircularOrder α] (σ τ : Equiv.Perm α)
    (hσ : σ ∈ MetaMathlibExt.circularOrderAutSubgroup α)
    (hτ : τ ∈ MetaMathlibExt.circularOrderAutSubgroup α) :
    σ * τ ∈ MetaMathlibExt.circularOrderAutSubgroup α :=
  Subgroup.mul_mem _ hσ hτ

example (α : Type*) [CircularOrder α] (σ : Equiv.Perm α)
    (hσ : σ ∈ MetaMathlibExt.circularOrderAutSubgroup α) :
    σ⁻¹ ∈ MetaMathlibExt.circularOrderAutSubgroup α :=
  Subgroup.inv_mem _ hσ
