/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Support weights of weighted projective space simplices

For two distinct support weights, the IDP necessary condition determines the larger weight.
Its remainder modulo the smaller weight distinguishes the two possible families.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Support form of the IDP necessary condition.** Let $r = (r_1, \dots, r_d)$ and
$x = (x_1, \dots, x_d)$ be tuples of natural numbers. The pair $(r, x)$ satisfies the support
form of the necessary condition when, for every index $j$,
$1 + \sum_{i=1}^{d} x_i (r_i \bmod r_j) = r_j$, where $r_i \bmod r_j$ is the remainder of $r_i$
on division by $r_j$, with the convention $r_i \bmod 0 = r_i$.

When every $x_i$ is positive, let $q$ be the weight vector in which each $r_i$ is repeated
$x_i$ times. Then this condition is equivalent to $1 + \sum_i (q_i \bmod q_j) = q_j$ for every
index $j$ of $q$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Corollary 1. -/
public def SatisfiesSupportIDPNecessary {d : ℕ} (r x : Fin d → ℕ) : Prop :=
  ∀ j, 1 + ∑ i, x i * (r i % r j) = r j

/-- **Classification of two-supported vectors satisfying the necessary condition.** Let
$r = (r_1, r_2)$ and $x = (x_1, x_2)$ be pairs of positive integers with $r_1 < r_2$. Then
$1 + \sum_{i=1}^{2} x_i (r_i \bmod r_j) = r_j$ holds for $j = 1, 2$ (the support form of the IDP
necessary condition) if and only if either $r = (1, 1 + x_1)$ or
$r = (1 + x_2, 1 + (1 + x_2)x_1)$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 8. -/
public theorem two_supported_classification (r x : Fin 2 → ℕ)
    (hrpos : ∀ i, 1 ≤ r i) (hxpos : ∀ i, 1 ≤ x i) (hrinc : StrictMono r) :
    SatisfiesSupportIDPNecessary r x ↔
      (r 0 = 1 ∧ r 1 = 1 + x 0) ∨
      (r 0 = 1 + x 1 ∧ r 1 = 1 + (1 + x 1) * x 0) := by
  have hlt : r 0 < r 1 := hrinc (by decide : (0 : Fin 2) < 1)
  simp only [SatisfiesSupportIDPNecessary, Fin.forall_fin_two, Fin.sum_univ_two, Nat.mod_self,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.mod_eq_of_lt hlt]
  constructor
  · rintro ⟨h₀, h₁⟩
    rcases eq_or_lt_of_le (hrpos 0) with h | h
    · exact Or.inl ⟨h.symm, by simpa [← h] using h₁.symm⟩
    · rw [← h₁, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h, Nat.mul_one] at h₀
      exact Or.inr ⟨h₀.symm, by rw [h₀, Nat.mul_comm, h₁]⟩
  · rintro (⟨h₀, h₁⟩ | ⟨h₀, h₁⟩)
    · simp [h₀, h₁, Nat.mod_one]
    · have h : 1 < 1 + x 1 := Nat.lt_add_of_pos_right (hxpos 1)
      simp [h₀, h₁, Nat.mod_eq_of_lt h, Nat.mul_comm]

end

end MetaMathlibExt
