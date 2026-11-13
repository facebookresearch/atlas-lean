/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Strict betweenness.** Let $\alpha$ be a type with a relation $<$ and let $a, b, c \in \alpha$.
Then $b$ lies strictly between $a$ and $c$ when either $a < b$ and $b < c$, or $c < b$ and
$b < a$. -/
def isBetween (α : Type*) [LT α] (a b c : α) : Prop :=
  (a < b ∧ b < c) ∨ (c < b ∧ b < a)

/-- **The betweenness automorphism group of a linear order.** Let $\alpha$ be a linearly ordered
set, and say that $b$ lies strictly between $a$ and $c$ when $a < b < c$ or $c < b < a$. The
betweenness automorphism group of $\alpha$ is the subgroup of the group of permutations of
$\alpha$ consisting of the permutations $\sigma$ such that, for all $a, b, c \in \alpha$, $b$ lies
strictly between $a$ and $c$ if and only if $\sigma(b)$ lies strictly between $\sigma(a)$ and
$\sigma(c)$. -/
def betweennessAutSubgroup (α : Type*) [LinearOrder α] : Subgroup (Equiv.Perm α) where
  carrier := { σ | ∀ a b c : α, isBetween α a b c ↔ isBetween α (σ a) (σ b) (σ c) }
  mul_mem' := by
    intro σ τ hσ hτ a b c
    change isBetween α a b c ↔
      isBetween α (σ (τ a)) (σ (τ b)) (σ (τ c))
    exact (hτ a b c).trans (hσ (τ a) (τ b) (τ c))
  one_mem' := by
    intro a b c
    simp [Equiv.Perm.coe_one, isBetween]
  inv_mem' := by
    intro σ hσ a b c
    have h := hσ (σ⁻¹ a) (σ⁻¹ b) (σ⁻¹ c)
    simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using h.symm

end

end MetaMathlibExt
