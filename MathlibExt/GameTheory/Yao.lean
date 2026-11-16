/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators

/-!
# Yao's principle by averaging

For a finite cost matrix and distributions over algorithms
and inputs, some deterministic algorithm costs at most the
mixed expectation under any input distribution, and some
input costs at least the mixed expectation. The paging
lower bound is not included here.
-/

@[expose] public section

/-- Yao's principle, averaging form (ALG-25b core). `C a y`
is the cost of deterministic algorithm `a` on input `y`;
`p` is a distribution over algorithms and `q` over inputs.
There is a deterministic algorithm whose expected cost
under `q` is at most the mixed expected cost, and an input
whose expected cost under `p` is at least the mixed
expected cost. Randomized lower bounds follow by applying
the second statement to an input distribution certifying
hardness. -/
theorem yao_exists_det {A Y : Type*} [Fintype A] [Fintype Y]
    [Nonempty A] (C : A → Y → ℚ) (p q : A → ℚ) (r : Y → ℚ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    ∃ a, (∑ y, r y * C a y)
      ≤ ∑ a', p a' * (∑ y, r y * C a' y) := by
  obtain ⟨a₀, -, hmin⟩ :=
    Finset.exists_min_image Finset.univ (fun a => ∑ y, r y * C a y)
      Finset.univ_nonempty
  refine ⟨a₀, ?_⟩
  calc (∑ y, r y * C a₀ y)
      = (∑ a', p a') * (∑ y, r y * C a₀ y) := by rw [hp1, one_mul]
    _ = ∑ a', p a' * (∑ y, r y * C a₀ y) := by rw [Finset.sum_mul]
    _ ≤ ∑ a', p a' * (∑ y, r y * C a' y) :=
        Finset.sum_le_sum fun a' _ =>
          mul_le_mul_of_nonneg_left (hmin a' (Finset.mem_univ a')) (hp0 a')

/-- The input-side averaging statement. -/
theorem yao_exists_input {A Y : Type*} [Fintype A] [Fintype Y]
    [Nonempty Y] (C : A → Y → ℚ) (p : A → ℚ) (r : Y → ℚ)
    (hr0 : ∀ y, 0 ≤ r y) (hr1 : ∑ y, r y = 1) :
    ∃ y, (∑ a, p a * C a y)
      ≥ ∑ y', r y' * (∑ a, p a * C a y') := by
  obtain ⟨y₀, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun y => ∑ a, p a * C a y)
      Finset.univ_nonempty
  refine ⟨y₀, ?_⟩
  calc (∑ a, p a * C a y₀)
      = (∑ y', r y') * (∑ a, p a * C a y₀) := by rw [hr1, one_mul]
    _ = ∑ y', r y' * (∑ a, p a * C a y₀) := by rw [Finset.sum_mul]
    _ ≥ ∑ y', r y' * (∑ a, p a * C a y') :=
        Finset.sum_le_sum fun y' _ =>
          mul_le_mul_of_nonneg_left (hmax y' (Finset.mem_univ y')) (hr0 y')

end
