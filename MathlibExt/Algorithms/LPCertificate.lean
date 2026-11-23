/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Ring

/-!
# LP optimality certificates

For the equality-form linear program over `ℚ` that maximizes `∑ j, c j * x j` subject to
`∑ j, A i j * x j = b i` for every `i` and `x ≥ 0`, a dual vector `y` with
`c j ≤ ∑ i, y i * A i j` for every `j` that satisfies complementary slackness with a feasible
point `x` certifies that `x` is optimal.

The inequality-form analogue over `ℝ`, which certifies optimality by equal primal and dual
objectives instead of complementary slackness, is
`MathlibExt.Analysis.Convex.LPCertificate.feasible_pair_equal_objectives_optimal`.
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

/-- Optimality certificate for an equality-form LP: maximize `∑ j, c j * x j` subject to
`∑ j, A i j * x j = b i` for every `i` and `x ≥ 0`. Let `x` be feasible (`_hx0`, `hxb`), let
the dual vector `y` satisfy `c j ≤ ∑ i, y i * A i j` for every `j` (`hyA`), and let
complementary slackness `x j * ((∑ i, y i * A i j) - c j) = 0` hold for every `j` (`hcs`).
Then every feasible `x'` has objective at most that of `x`, so `x` is optimal. Both objectives
are compared with the dual objective `∑ i, y i * b i`; the bound itself does not use `_hx0`,
which only makes `x` feasible. -/
theorem lp_optimal_of_certificate {m n : ℕ}
    (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (c : Fin n → ℚ)
    (x : Fin n → ℚ) (y : Fin m → ℚ)
    (_hx0 : ∀ j, 0 ≤ x j)
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
