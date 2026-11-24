/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MechanismDesign.SingleParameter
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

open Set MathlibExt.GameTheory.MechanismDesign.SingleParameter

/-- Linear allocation `Q t = t` with payment `P t = t ^ 2 / 2` is incentive compatible on
`[0, 1]`. -/
theorem linear_isIC : IsIncentiveCompatibleOn (fun t => t) (fun t => t ^ 2 / 2) 0 1 := by
  intro s _ t _
  simp only [truthfulUtility]
  nlinarith [sq_nonneg (t - s)]

/-- Myerson's lemma recovers its monotonicity and its envelope formula. -/
example : MonotoneOn (fun t : ℝ => t) (Icc 0 1) :=
  (isIncentiveCompatibleOn_iff.1 linear_isIC).1

example : truthfulUtility (fun t => t) (fun t => t ^ 2 / 2) 1 =
    truthfulUtility (fun t => t) (fun t => t ^ 2 / 2) 0 + ∫ x in (0 : ℝ)..1, x :=
  linear_isIC.envelope_formula ⟨by norm_num, le_rfl⟩

/-- A decreasing allocation cannot be implemented, whatever the payments. -/
example (P : ℝ → ℝ) : ¬IsIncentiveCompatibleOn (fun t => 1 - t) P 0 1 := by
  intro h
  have := h.allocation_monotoneOn (a := (0 : ℝ)) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  norm_num at this

/-- Revenue equivalence: adding a constant to the payment of an incentive-compatible mechanism
keeps it incentive compatible, and the payments then agree exactly when they agree at the lowest
value. -/
example (c : ℝ) (hc : (0 : ℝ) ^ 2 / 2 = 0 ^ 2 / 2 + c) :
    EqOn (fun t : ℝ => t ^ 2 / 2) (fun t => t ^ 2 / 2 + c) (Icc 0 1) := by
  have h2 : IsIncentiveCompatibleOn (fun t => t) (fun t => t ^ 2 / 2 + c) 0 1 := by
    intro s _ t _
    simp only [truthfulUtility]
    nlinarith [sq_nonneg (t - s)]
  exact payment_eqOn_of_isIncentiveCompatibleOn linear_isIC h2 hc

/-- Individual rationality propagates from the lowest type. -/
example {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ truthfulUtility (fun t => t) (fun t => t ^ 2 / 2) t :=
  linear_isIC.utility_nonneg_of_lowest (fun t ht => ht.1) (by simp [truthfulUtility]) ht
