/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic.Positivity

/-! # Multiplicities in Beatty sequences -/

namespace MetaMathlibExt

namespace beatty_floor_fiber_card_succ_iff

/-- Positive indices giving the value `t` form a half-open interval of naturals. -/
private theorem fiber_card {a : ℝ} (ha : 0 < a) (t : ℕ) :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * a⌋ = t}.ncard =
      ⌈((t + 1 : ℕ) : ℝ) / a⌉₊ - max 1 ⌈(t : ℝ) / a⌉₊ := by
  rw [← Set.ncard_Ico_nat]
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, Int.floor_eq_iff, Int.cast_natCast, Set.mem_Ico, max_le_iff,
    Nat.ceil_le, Nat.lt_ceil, div_le_iff₀ ha, lt_div_iff₀ ha, Nat.cast_add_one, and_assoc,
    Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

end beatty_floor_fiber_card_succ_iff

/-- **Multiplicity $k + 1$ for $\alpha$ is multiplicity $k$ for $\alpha/(1 - \alpha)$.** Let $k$ be
a positive integer, let $\alpha$ be a real number with $1/(k + 1) < \alpha < 1/k$, and let
$\beta = \alpha/(1 - \alpha)$. Then a non-negative integer $t$ equals $\lfloor n\alpha\rfloor$ for
exactly $k + 1$ positive integers $n$ if and only if it equals $\lfloor n\beta\rfloor$ for exactly
$k$ positive integers $n$.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 2 (`integers-2025-A104-lem-2`). -/
public theorem beatty_floor_fiber_card_succ_iff {α : ℝ} {k : ℕ}
    (h1 : 1 / ((k : ℝ) + 1) < α) (h2 : α < 1 / (k : ℝ)) (t : ℕ) :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1 ↔
      {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (α / (1 - α))⌋ = t}.ncard = k := by
  have hα : 0 < α := lt_trans (by positivity) h1
  have hlt : α < 1 := by
    cases k with
    | zero => simpa using h2.trans_le (by norm_num)
    | succ k => exact h2.trans_le ((div_le_one (by positivity)).2 (by simp))
  let β := α / (1 - α)
  have hβ : 0 < β := div_pos hα (sub_pos.mpr hlt)
  -- The endpoints for α are the endpoints for β translated by an integer.
  have shift (m : ℕ) : ⌈(m : ℝ) / α⌉₊ = ⌈(m : ℝ) / β⌉₊ + m := by
    have heq : (m : ℝ) / α = m / β + m := by
      simp [β, div_div_eq_mul_div, mul_sub, sub_div, hα.ne']
    rw [heq, Nat.ceil_add_natCast (by positivity)]
  rw [beatty_floor_fiber_card_succ_iff.fiber_card hα,
    beatty_floor_fiber_card_succ_iff.fiber_card hβ, shift, shift]
  have hmono : ⌈(t : ℝ) / β⌉₊ ≤ ⌈((t + 1 : ℕ) : ℝ) / β⌉₊ := by
    apply Nat.ceil_le_ceil
    gcongr
    exact Nat.le_succ t
  have hupper : 0 < ⌈((t + 1 : ℕ) : ℝ) / β⌉₊ := Nat.ceil_pos.mpr (by positivity)
  by_cases ht : t = 0
  · omega
  · have hlower : 0 < ⌈(t : ℝ) / β⌉₊ :=
      Nat.ceil_pos.mpr (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero ht)) hβ)
    omega

end MetaMathlibExt
