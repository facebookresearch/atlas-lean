/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Best responses in zero-sum games

Some pure strategy is a best response to any mixed
strategy, and a saddle point is a Nash equilibrium of the
zero-sum game. General Nash existence is not included
here.
-/

@[expose] public section

/-- Expected payoff of mixed strategies in a finite
two-player zero-sum game (DPA-44 core). -/
noncomputable def expPayoff {m n : ℕ} (u : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * q j * u i j

/-- A pure best response to `q` is at least as good as any
mixed strategy: some row maximizes the row value against
`q`, and mixing cannot beat it. -/
theorem exists_pure_best_response {m n : ℕ} [Nonempty (Fin m)]
    (u : Fin m → Fin n → ℝ) (q : Fin n → ℝ)
    (p : Fin m → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    ∃ i : Fin m, expPayoff u p q ≤ ∑ j, q j * u i j := by
  obtain ⟨i₀, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => ∑ j, q j * u i j) Finset.univ_nonempty
  refine ⟨i₀, ?_⟩
  calc expPayoff u p q
      = ∑ i, p i * (∑ j, q j * u i j) := by
        unfold expPayoff
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ ≤ ∑ i, p i * (∑ j, q j * u i₀ j) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hmax i (Finset.mem_univ i)) (hp0 i)
    _ = ∑ j, q j * u i₀ j := by
        rw [← Finset.sum_mul, hp1, one_mul]

/-- In a zero-sum game, a saddle point is a Nash
equilibrium: neither player gains by unilateral deviation
(player two's payoff is the negative expectation). -/
theorem saddle_is_nash {m n : ℕ} (u : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (q : Fin n → ℝ)
    (hmax : ∀ p', expPayoff u p' q ≤ expPayoff u p q)
    (hmin : ∀ q', expPayoff u p q ≤ expPayoff u p q') :
    (∀ p', expPayoff u p' q ≤ expPayoff u p q)
    ∧ (∀ q', -expPayoff u p q' ≤ -expPayoff u p q) := by
  exact ⟨hmax, fun q' => neg_le_neg (hmin q')⟩

end
