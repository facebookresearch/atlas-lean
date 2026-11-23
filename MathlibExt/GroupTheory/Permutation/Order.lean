/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Perm.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Order automorphism group.** For a type $\alpha$ equipped with a relation $<$, the order
automorphism group of $\alpha$ is the subgroup of the group of permutations of $\alpha$
consisting of the permutations $\sigma$ such that for all $a, b \in \alpha$, $a < b$ holds if and
only if $\sigma(a) < \sigma(b)$ holds. -/
def orderAutSubgroup (α : Type*) [LT α] : Subgroup (Equiv.Perm α) where
  carrier := {σ | ∀ a b, a < b ↔ σ a < σ b}
  one_mem' a b := by simp
  mul_mem' hσ hτ a b := (hτ a b).trans (hσ _ _)
  inv_mem' {σ} h a b := by simpa using (h (σ⁻¹ a) (σ⁻¹ b)).symm

@[simp]
public theorem mem_orderAutSubgroup {α : Type*} [LT α] (σ : Equiv.Perm α) :
    σ ∈ orderAutSubgroup α ↔ ∀ a b, a < b ↔ σ a < σ b :=
  Iff.rfl

end

end MetaMathlibExt
