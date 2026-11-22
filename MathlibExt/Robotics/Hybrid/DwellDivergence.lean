/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Field

import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Positive dwell time implies divergence

If every step duration is at least a fixed positive dwell
`δ`, the elapsed time after `n` steps is at least `n * δ`
and therefore tends to infinity. Consequently only finitely
many steps end before any finite horizon `H`, each such
step count `n` satisfying `n * δ ≤ H`.
-/

@[expose] public section

namespace Robotics.Hybrid

/-- Elapsed time after `n` steps of a duration sequence. -/
def dwellElapsed (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, d k

/-- Positive dwell gives a linear lower bound on elapsed
time: if every duration is at least `δ`, then after `n`
steps the elapsed time is at least `n * δ`. -/
theorem dwellElapsed_ge {d : ℕ → ℝ} {δ : ℝ}
    (hd : ∀ k, δ ≤ d k) (n : ℕ) :
    (n : ℝ) * δ ≤ dwellElapsed d n := by
  unfold dwellElapsed
  have h : (∑ _k ∈ Finset.range n, δ) = (n : ℝ) * δ := by
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← h]
  exact Finset.sum_le_sum fun k _ => hd k

/-- Positive dwell implies physical divergence: if every
duration is at least some `δ > 0`, the elapsed time tends
to infinity. -/
theorem dwellElapsed_tendsto_atTop {d : ℕ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hd : ∀ k, δ ≤ d k) :
    Filter.Tendsto (dwellElapsed d) Filter.atTop Filter.atTop := by
  have hbound : Filter.Tendsto (fun n : ℕ => (n : ℝ) * δ) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hδ tendsto_natCast_atTop_atTop
  exact Filter.tendsto_atTop_mono (fun n => dwellElapsed_ge hd n) hbound

/-- **Finite-event criterion.** If every step duration `d k` is at least `δ > 0`, only finitely
many events occur up to any horizon `H`: every step count `n` with elapsed time
`dwellElapsed d n ≤ H` satisfies `n δ ≤ H`. -/
lemma events_finite_of_dwell {d : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hd : ∀ k, δ ≤ d k) (H : ℝ) :
    {n : ℕ | dwellElapsed d n ≤ H}.Finite ∧ ∀ n, dwellElapsed d n ≤ H → (n : ℝ) * δ ≤ H := by
  have hbound : ∀ n, dwellElapsed d n ≤ H → (n : ℝ) ≤ H / δ := by
    intro n hn
    rw [le_div_iff₀ hδ]
    exact le_trans (dwellElapsed_ge hd n) hn
  refine ⟨?_, fun n hn => le_trans (dwellElapsed_ge hd n) hn⟩
  refine Set.Finite.subset (Set.finite_lt_nat (⌊H / δ⌋₊ + 1)) ?_
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn ⊢
  have h2 : (n : ℝ) ≤ H / δ := hbound n hn
  have h3 : n ≤ ⌊H / δ⌋₊ := Nat.le_floor h2
  omega

end Robotics.Hybrid
