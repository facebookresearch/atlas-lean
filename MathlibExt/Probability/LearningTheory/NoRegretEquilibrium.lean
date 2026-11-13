/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section



/-- Bilinear payoff of mixed strategies `p`, `q` in the matrix
game `A`. -/
def mixedPayoff {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * q j * A i j

/-- The time average of a sequence of strategies over `T`
rounds. -/
noncomputable def avgStrat {T : ℕ} {ι : Type*} (p : Fin T → ι → ℝ) (i : ι) :
    ℝ :=
  (∑ t, p t i) / T

/-- Payoff of the average strategy against `y` is the average of
the per-round payoffs (bilinearity, left argument). -/
theorem mixedPayoff_avg_left {m n T : ℕ} (A : Fin m → Fin n → ℝ)
    (p : Fin T → Fin m → ℝ) (y : Fin n → ℝ) (hT : (T : ℝ) ≠ 0) :
    mixedPayoff A (avgStrat p) y =
      (∑ t, mixedPayoff A (p t) y) / T := by
  unfold mixedPayoff avgStrat
  have hpush : ∀ i : Fin m, ∀ j : Fin n,
      (∑ t, p t i) / (T : ℝ) * y j * A i j =
        (∑ t, p t i * y j * A i j) / T := by
    intro i j
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  simp only [hpush, ← Finset.sum_div]
  congr 1
  calc (∑ i, ∑ j, ∑ t, p t i * y j * A i j)
      = ∑ i, ∑ t, ∑ j, p t i * y j * A i j := by
        apply Finset.sum_congr rfl; intro i _
        exact Finset.sum_comm
    _ = ∑ t, ∑ i, ∑ j, p t i * y j * A i j := Finset.sum_comm

/-- Payoff of `x` against the average strategy is the average of
the per-round payoffs (bilinearity, right argument). -/
theorem mixedPayoff_avg_right {m n T : ℕ} (A : Fin m → Fin n → ℝ)
    (x : Fin m → ℝ) (q : Fin T → Fin n → ℝ) (hT : (T : ℝ) ≠ 0) :
    mixedPayoff A x (avgStrat q) =
      (∑ t, mixedPayoff A x (q t)) / T := by
  unfold mixedPayoff avgStrat
  have hpush : ∀ i : Fin m, ∀ j : Fin n,
      x i * ((∑ t, q t j) / (T : ℝ)) * A i j =
        (∑ t, x i * q t j * A i j) / T := by
    intro i j
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  simp only [hpush, ← Finset.sum_div]
  congr 1
  calc (∑ i, ∑ j, ∑ t, x i * q t j * A i j)
      = ∑ i, ∑ t, ∑ j, x i * q t j * A i j := by
        apply Finset.sum_congr rfl; intro i _
        exact Finset.sum_comm
    _ = ∑ t, ∑ i, ∑ j, x i * q t j * A i j := Finset.sum_comm

/-- No-regret dynamics: if the row player's average regret is at
most `ε₁` and the column player's is at most `ε₂`, then the
averaged strategies form an `(ε₁ + ε₂)`-approximate saddle
point: no deviation gains more than `ε₁ + ε₂`. -/
theorem no_regret_approx_saddle {m n T : ℕ} (A : Fin m → Fin n → ℝ)
    (p : Fin T → Fin m → ℝ) (q : Fin T → Fin n → ℝ)
    (ε₁ ε₂ : ℝ) (hT : (T : ℝ) ≠ 0)
    (hrow : ∀ y : Fin n → ℝ,
      (∑ t, mixedPayoff A (p t) y) / T -
        (∑ t, mixedPayoff A (p t) (q t)) / T ≤ ε₁)
    (hcol : ∀ x : Fin m → ℝ,
      (∑ t, mixedPayoff A (p t) (q t)) / T -
        (∑ t, mixedPayoff A x (q t)) / T ≤ ε₂) :
    ∀ (x : Fin m → ℝ) (y : Fin n → ℝ),
      mixedPayoff A (avgStrat p) y -
        mixedPayoff A x (avgStrat q) ≤ ε₁ + ε₂ := by
  intro x y
  rw [mixedPayoff_avg_left A p y hT, mixedPayoff_avg_right A x q hT]
  have hr := hrow y
  have hc := hcol x
  linarith
