/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Flash balance and the Rachford–Rice equation

For finitely many components and stipulated positive equilibrium ratios, the phase
compositions follow from the steady flow balance. Their difference in total composition
is the Rachford–Rice objective. Together with the feed normalization, its vanishing
characterizes simultaneous phase normalization, including at vapour fractions zero and one.
-/

open scoped BigOperators

namespace Domains.Chemistry.Separations.RachfordRiceBalance

/-- For a positive feed with normalized composition and stipulated positive `K`, the
component balances determine both phase compositions at every vapour fraction in `[0, 1]`.
The denominators are positive even at the endpoints. Both phase compositions sum to one
exactly when the Rachford–Rice objective is zero. This does not assert existence of a root
or derive the `K` values from a thermodynamic model.

Source for the objective: Adewumi, *Phase Relations in Reservoir Engineering*, §13.2. -/
public theorem flash_balance_rachford_rice {ι : Type*} [Fintype ι] (F L V : ℝ)
    (z K x y : ι → ℝ) (hF : 0 < F) (hflow : F = L + V)
    (hβ : 0 ≤ V / F ∧ V / F ≤ 1) (_hz₀ : ∀ i, 0 ≤ z i) (hz : ∑ i, z i = 1)
    (hK : ∀ i, 0 < K i) (hmix : ∀ i, F * z i = L * x i + V * y i)
    (heq : ∀ i, y i = K i * x i) :
    let β := V / F
    let D := fun i => 1 + β * (K i - 1)
    (∀ i, 0 < D i ∧ x i = z i / D i ∧ y i = K i * (z i / D i)) ∧
    (((∑ i, x i) = 1 ∧ (∑ i, y i) = 1) ↔ ∑ i, z i * (K i - 1) / D i = 0) := by
  intro β D
  have hV : β * F = V := div_mul_cancel₀ _ hF.ne'
  have hL : (1 - β) * F = L := by
    rw [sub_mul, one_mul, hV, hflow, add_sub_cancel_right]
  have hbal (i : ι) : z i = (1 - β) * x i + β * y i := by
    apply mul_left_cancel₀ hF.ne'
    calc
      F * z i = L * x i + V * y i := hmix i
      _ = F * ((1 - β) * x i + β * y i) := by rw [← hL, ← hV]; ring
  have hdecomp (i : ι) : D i = (1 - β) + β * K i := by
    change 1 + β * (K i - 1) = _
    ring
  have hpos (i : ι) : 0 < D i := by
    rw [hdecomp]
    by_cases hzero : β = 0
    · simp [hzero]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hβ.2)
        (mul_pos (lt_of_le_of_ne hβ.1 (Ne.symm hzero)) (hK i))
  have hx (i : ι) : x i = z i / D i := by
    apply (eq_div_iff (hpos i).ne').2
    calc
      x i * D i = (1 - β) * x i + β * y i := by rw [hdecomp, heq]; ring
      _ = z i := (hbal i).symm
  have hobj : (∑ i, z i * (K i - 1) / D i) = (∑ i, y i) - (∑ i, x i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [heq, hx]
    simp only [div_eq_mul_inv]
    ring
  refine ⟨fun i => ⟨hpos i, hx i, (heq i).trans (congrArg (K i * ·) (hx i))⟩, ?_⟩
  rw [hobj]
  constructor
  · rintro ⟨hxn, hyn⟩
    rw [hxn, hyn, sub_self]
  · intro hzero
    have hyx := sub_eq_zero.mp hzero
    have htotal : (1 - β) * (∑ i, x i) + β * (∑ i, y i) = 1 := by
      calc
        _ = ∑ i, ((1 - β) * x i + β * y i) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
        _ = ∑ i, z i := Finset.sum_congr rfl fun i _ => (hbal i).symm
        _ = 1 := hz
    rw [hyx] at htotal
    have hxn : (∑ i, x i) = 1 := by
      calc
        _ = (1 - β) * (∑ i, x i) + β * (∑ i, x i) := by ring
        _ = 1 := htotal
    exact ⟨hxn, hyx.trans hxn⟩

end Domains.Chemistry.Separations.RachfordRiceBalance
