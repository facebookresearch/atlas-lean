/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finset.Max

/-!
# Yao's principle by averaging

`C a y` is the cost of deterministic algorithm `a` on input `y`, for finite
types of algorithms and inputs. These are the two averaging steps behind the
easy direction of Yao's minimax principle:

* `yao_exists_det`: for a distribution `p` over algorithms and any input
  weights `q`, some deterministic algorithm has `q`-weighted cost at most the
  `p`-average of those costs.
* `yao_exists_input`: for a distribution `q` over inputs and any algorithm
  weights `p`, some input has `p`-weighted cost at least the `q`-average of
  those costs.

The paging lower bound is not included here.

## References

* A. C.-C. Yao, *Probabilistic computations: Toward a unified measure of
  complexity*, 18th Annual Symposium on Foundations of Computer Science
  (FOCS), 1977.
* R. Motwani and P. Raghavan, *Randomized Algorithms*, Cambridge University
  Press, 1995, Section 2.2.
-/

@[expose] public section

namespace MathlibExt.GameTheory.Yao

/-- Deterministic side of Yao's principle by averaging. `C a y` is the cost of
deterministic algorithm `a` on input `y`, `p` is a distribution over
algorithms, and `q : Y → ℚ` weights the inputs (typically an input
distribution, but no condition on `q` is needed). Some deterministic
algorithm's `q`-weighted cost is at most the `p`-average of the algorithms'
`q`-weighted costs. -/
theorem yao_exists_det {A Y : Type*} [Fintype A] [Fintype Y]
    [Nonempty A] (C : A → Y → ℚ) (p : A → ℚ) (q : Y → ℚ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    ∃ a, (∑ y, q y * C a y)
      ≤ ∑ a', p a' * (∑ y, q y * C a' y) := by
  obtain ⟨a₀, -, hmin⟩ :=
    Finset.exists_min_image Finset.univ (fun a => ∑ y, q y * C a y)
      Finset.univ_nonempty
  refine ⟨a₀, ?_⟩
  calc (∑ y, q y * C a₀ y)
      = (∑ a', p a') * (∑ y, q y * C a₀ y) := by rw [hp1, one_mul]
    _ = ∑ a', p a' * (∑ y, q y * C a₀ y) := by rw [Finset.sum_mul]
    _ ≤ ∑ a', p a' * (∑ y, q y * C a' y) :=
        Finset.sum_le_sum fun a' _ =>
          mul_le_mul_of_nonneg_left (hmin a' (Finset.mem_univ a')) (hp0 a')

/-- Input side of Yao's principle by averaging. `C a y` is the cost of
deterministic algorithm `a` on input `y`, `q` is a distribution over inputs,
and `p : A → ℚ` weights the algorithms (typically an algorithm distribution,
but no condition on `p` is needed). Some input's `p`-weighted cost is at least
the `q`-average of the inputs' `p`-weighted costs. -/
theorem yao_exists_input {A Y : Type*} [Fintype A] [Fintype Y]
    [Nonempty Y] (C : A → Y → ℚ) (p : A → ℚ) (q : Y → ℚ)
    (hq0 : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1) :
    ∃ y, (∑ a, p a * C a y)
      ≥ ∑ y', q y' * (∑ a, p a * C a y') := by
  obtain ⟨y₀, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun y => ∑ a, p a * C a y)
      Finset.univ_nonempty
  refine ⟨y₀, ?_⟩
  calc (∑ a, p a * C a y₀)
      = (∑ y', q y') * (∑ a, p a * C a y₀) := by rw [hq1, one_mul]
    _ = ∑ y', q y' * (∑ a, p a * C a y₀) := by rw [Finset.sum_mul]
    _ ≥ ∑ y', q y' * (∑ a, p a * C a y') :=
        Finset.sum_le_sum fun y' _ =>
          mul_le_mul_of_nonneg_left (hmax y' (Finset.mem_univ y')) (hq0 y')

end MathlibExt.GameTheory.Yao

end
