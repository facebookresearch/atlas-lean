/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Tactic.Ring

/-!
# LP optimality certificates

A feasible dual vector with complementary slackness
certifies optimality of a feasible primal point. Phase I
initialization is not included here.
-/

@[expose] public section

private theorem sum_dual_mul {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (y : Fin m → ℚ) (z : Fin n → ℚ) (b : Fin m → ℚ)
    (hzb : ∀ i, ∑ j, A i j * z j = b i) :
    ∑ j, (∑ i, y i * A i j) * z j = ∑ i, y i * b i := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have h : (∑ j, (y i * A i j) * z j) = y i * (∑ j, A i j * z j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h, hzb i]

/-- Optimality certificates for standard-form LPs
(ALG-30c core). The primal is `A x = b`, `x ≥ 0`, maximize
`c · x`. A dual vector `y` with `y A ≥ c` certifies that
the feasible point `x` is optimal when complementary
slackness holds: `x j * ((y A) j - c j) = 0` for all `j`
and `y i * ((A x) i - b i) = 0` for all `i` (the second is
automatic from feasibility but is the certificate's
primal half). Phase I initialization is downstream. -/
theorem lp_optimal_of_certificate {m n : ℕ}
    (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (c : Fin n → ℚ)
    (x : Fin n → ℚ) (y : Fin m → ℚ)
    (hx0 : ∀ j, 0 ≤ x j)
    (hxb : ∀ i, ∑ j, A i j * x j = b i)
    (hyA : ∀ j, c j ≤ ∑ i, y i * A i j)
    (hcs : ∀ j, x j * ((∑ i, y i * A i j) - c j) = 0)
    (x' : Fin n → ℚ)
    (hx'0 : ∀ j, 0 ≤ x' j)
    (hx'b : ∀ i, ∑ j, A i j * x' j = b i) :
    ∑ j, c j * x' j ≤ ∑ j, c j * x j := by
  have h1 : ∑ j, c j * x' j ≤ ∑ j, (∑ i, y i * A i j) * x' j := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (hyA j) (hx'0 j)
  have h2 : ∑ j, (∑ i, y i * A i j) * x' j = ∑ i, y i * b i :=
    sum_dual_mul A y x' b hx'b
  have h4 : ∑ j, (∑ i, y i * A i j) * x j = ∑ i, y i * b i :=
    sum_dual_mul A y x b hxb
  have h3 : ∑ j, (∑ i, y i * A i j) * x j = ∑ j, c j * x j := by
    apply Finset.sum_congr rfl
    intro j _
    have h := hcs j
    rw [mul_eq_zero] at h
    cases h with
    | inl hxj =>
      rw [hxj]
      ring
    | inr hsub =>
      have heq : (∑ i, y i * A i j) = c j := sub_eq_zero.mp hsub
      rw [heq]
  calc ∑ j, c j * x' j ≤ ∑ j, (∑ i, y i * A i j) * x' j := h1
    _ = ∑ i, y i * b i := h2
    _ = ∑ j, (∑ i, y i * A i j) * x j := h4.symm
    _ = ∑ j, c j * x j := h3

end
