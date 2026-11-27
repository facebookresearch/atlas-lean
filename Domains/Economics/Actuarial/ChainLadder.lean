/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Chain-ladder completion of a run-off triangle

The input contains only observed cumulative claims. Each age-to-age factor is the ratio of two
column totals over the same accident years, not an unweighted average of individual ratios.
Completion copies observed cells and advances each incomplete row one development year at a time.
`chainLadderCompletion` gives the product formula and, for nondecreasing observed rows with
nonnegative claims and positive paired denominators, the factor and reserve bounds.

## Reference

T. Mack, *Distribution-free calculation of the standard error of chain ladder reserve estimates*,
ASTIN Bulletin 23(2) (1993), 213–225, §2, pp. 214–215. With `I = n + 1`, the paper's accident and
development years are our indices plus one. We use the displayed estimators, not the stochastic
assumptions or standard-error results. The sign bounds below are deterministic consequences.
-/

@[expose] public noncomputable section

namespace Domains.Economics.Actuarial.ChainLadder

open Finset

/-- Cumulative claims on the observed triangle. An unobserved cell has no input value. -/
abbrev Triangle (n : ℕ) := (i j : ℕ) → i + j ≤ n → ℝ

variable {n : ℕ} (C : Triangle n)

/-- Total at age `j` for precisely the accident years with a known value at age `j + 1`. -/
def pairedBase (j : Fin n) : ℝ :=
  ∑ i : Fin (n - j.val), C i j (by have := i.isLt; omega)

/-- Estimated development factor from `j` to `j + 1`. The denominator is a column total,
not an individual claim. As usual in `ℝ`, division is total; the method uses positive totals. -/
def factor (j : Fin n) : ℝ :=
  (∑ i : Fin (n - j.val), C i (j.val + 1) (by have := i.isLt; omega)) / pairedBase C j

/-- Latest observed cumulative claim in accident year `i`, at development age `n - i`. -/
def latest (i : Fin (n + 1)) : ℝ := C i (n - i.val) (by have := i.isLt; omega)

/-- Complete a row by retaining each observation and multiplying the preceding estimate by
one fitted factor at each unobserved successor. -/
def complete (i : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  Fin.induction (C i 0 (by have := i.isLt; omega)) fun j prev ↦
    if h : i.val + j.succ.val ≤ n then C i j.succ h else prev * factor C j

/-- Every observed cell, not just the latest one, is unchanged by completion. -/
theorem complete_observed (i j : Fin (n + 1)) (h : i.val + j.val ≤ n) :
    complete C i j = C i j h := by
  induction j using Fin.induction with
  | zero => rfl
  | succ j _ =>
    change i.val + (j.val + 1) ≤ n at h
    simp [complete, h]

/-- The step from the diagonal or any later age multiplies by the factor for that age. -/
theorem complete_succ (i : Fin (n + 1)) (j : Fin n) (h : n - i.val ≤ j.val) :
    complete C i j.succ = complete C i j.castSucc * factor C j := by
  have hnot : ¬ i.val + (j.val + 1) ≤ n := by omega
  simp [complete, hnot]

/-- Product of the fitted factors at ages in the half-open interval `[a, b)`. -/
def factorProduct (a b : ℕ) : ℝ := ∏ k : Fin n with a ≤ k.val ∧ k.val < b, factor C k

private theorem factorProduct_self (a : ℕ) : factorProduct C a a = 1 := by
  apply prod_eq_one
  intro k hk
  obtain ⟨hle, hlt⟩ := (mem_filter.mp hk).2
  omega

private theorem factorProduct_succ (a : ℕ) (j : Fin n) (h : a ≤ j.val) :
    factorProduct C a (j.val + 1) = factorProduct C a j.val * factor C j := by
  have hs : (univ.filter fun k : Fin n ↦ a ≤ k.val ∧ k.val < j.val + 1) =
      insert j (univ.filter fun k : Fin n ↦ a ≤ k.val ∧ k.val < j.val) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  unfold factorProduct
  rw [hs, prod_insert (by simp), mul_comm]

/-- On or after the diagonal the completed claim is the latest observed claim times all
fitted factors from age `n - i` up to but not including the target age. -/
theorem complete_eq_prod (i j : Fin (n + 1)) (h : n - i.val ≤ j.val) :
    complete C i j = latest C i * factorProduct C (n - i.val) j.val := by
  have diagonal (k : Fin (n + 1)) (he : k.val = n - i.val) :
      complete C i k = latest C i * factorProduct C (n - i.val) k.val := by
    obtain rfl : k = ⟨n - i.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := Fin.ext he
    rw [complete_observed C _ _ (by dsimp; have := i.isLt; omega), factorProduct_self, mul_one]
    rfl
  induction j using Fin.induction with
  | zero => exact diagonal _ (by change 0 = _; change n - i.val ≤ 0 at h; omega)
  | succ j ih =>
    by_cases hj : n - i.val ≤ j.val
    · rw [complete_succ C i j hj, ih hj, Fin.val_castSucc, Fin.val_succ,
        factorProduct_succ C _ j hj, mul_assoc]
    · apply diagonal
      change j.val + 1 = _
      change n - i.val ≤ j.val + 1 at h
      omega

/-- Estimated outstanding claims in a row: its completed ultimate less its latest observation. -/
def reserve (i : Fin (n + 1)) : ℝ := complete C i (Fin.last n) - latest C i

/-- Observed cumulative amounts do not decrease across any adjacent observed pair in a row. -/
def Nondecreasing : Prop := ∀ i j (h : i + (j + 1) ≤ n), C i j (by omega) ≤ C i (j + 1) h

/-- If the observed rows are nondecreasing and the paired denominator at age `j` is strictly
positive, the fitted factor from age `j` to `j + 1` is at least one. -/
theorem one_le_factor (hmono : Nondecreasing C) (j : Fin n) (hpos : 0 < pairedBase C j) :
    1 ≤ factor C j := by
  apply (one_le_div hpos).mpr
  exact sum_le_sum fun i _ ↦ hmono i j (by have := i.isLt; omega)

/-- The estimated reserve is nonnegative if the latest claim is nonnegative, observed rows are
nondecreasing, and every paired denominator is positive. No individual cell need be positive. -/
theorem reserve_nonneg (hpos : ∀ j, 0 < pairedBase C j) (hmono : Nondecreasing C)
    (i : Fin (n + 1)) (hi : 0 ≤ latest C i) : 0 ≤ reserve C i := by
  unfold reserve
  rw [complete_eq_prod C i (Fin.last n) (by simp)]
  apply sub_nonneg.mpr
  apply le_mul_of_one_le_right hi
  exact one_le_prod₀ fun j _ ↦ one_le_factor C hmono j (hpos j)

/-- Classical chain-ladder completion: for nonnegative observed claims with positive paired
column totals, forecasts equal the last observation times the intervening factors. If observed
rows are nondecreasing, every fitted factor is at least one and every reserve is nonnegative. -/
theorem chainLadderCompletion (hpos : ∀ j, 0 < pairedBase C j)
    (hnonneg : ∀ i j h, 0 ≤ C i j h) :
    (∀ (i j : Fin (n + 1)), n - i.val ≤ j.val →
      complete C i j = latest C i * factorProduct C (n - i.val) j.val) ∧
    (Nondecreasing C → (∀ j, 1 ≤ factor C j) ∧ ∀ i, 0 ≤ reserve C i) :=
  ⟨complete_eq_prod C, fun hm ↦
    ⟨fun j ↦ one_le_factor C hm j (hpos j), fun i ↦ reserve_nonneg C hpos hm i (hnonneg ..)⟩⟩

end Domains.Economics.Actuarial.ChainLadder
