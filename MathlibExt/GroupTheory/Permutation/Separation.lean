/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Order.Circular

namespace MetaMathlibExt

@[expose] public section

/-- **Separation of pairs in a circular order.** Let $\alpha$ be a circular order, and write
$\operatorname{sbtw}(x, y, z)$ for its strict betweenness relation ($y$ lies strictly between
$x$ and $z$ going around the circle). For $a, b, c, d \in \alpha$, the pairs $a, b$ and $c, d$
separate each other when either $\operatorname{sbtw}(a, c, b)$ and $\operatorname{sbtw}(b, d, a)$
both hold, or $\operatorname{sbtw}(a, d, b)$ and $\operatorname{sbtw}(b, c, a)$ both hold. -/
def circularSeparates {α : Type*} [CircularOrder α] (a b c d : α) : Prop :=
  (sbtw a c b ∧ sbtw b d a) ∨ (sbtw a d b ∧ sbtw b c a)

/-- **Separation-preserving permutation group.** For a circular order $\alpha$, the
separation-preserving group of $\alpha$ is the subgroup of the group of permutations of $\alpha$
consisting of the permutations $\sigma$ such that for all $a, b, c, d \in \alpha$, the pairs
$a, b$ and $c, d$ separate each other if and only if the pairs $\sigma(a), \sigma(b)$ and
$\sigma(c), \sigma(d)$ separate each other. -/
def separationAutSubgroup (α : Type*) [CircularOrder α] : Subgroup (Equiv.Perm α) where
  carrier :=
    {σ | ∀ a b c d, circularSeparates a b c d ↔
      circularSeparates (σ a) (σ b) (σ c) (σ d)}
  one_mem' a b c d := by simp
  mul_mem' {σ τ} hσ hτ a b c d := by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    exact (hτ a b c d).trans (hσ _ _ _ _)
  inv_mem' {σ} hσ a b c d := by
    have h := (hσ (σ⁻¹ a) (σ⁻¹ b) (σ⁻¹ c) (σ⁻¹ d)).symm
    simpa [Equiv.apply_symm_apply] using h

@[simp]
theorem mem_separationAutSubgroup {α : Type*} [CircularOrder α] (σ : Equiv.Perm α) :
    σ ∈ separationAutSubgroup α ↔ ∀ a b c d, circularSeparates a b c d ↔
      circularSeparates (σ a) (σ b) (σ c) (σ d) :=
  Iff.rfl

end

end MetaMathlibExt
