/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Welfare.DeadweightLoss
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Linear monopoly: price, quantity and deadweight loss (Atlas EC17.T02)

A monopolist faces linear inverse demand `P q = a - b q` (`b > 0`) and constant
marginal cost `c < a` (the interior regime: some trade is efficient). Profit is
`(a - b q) q - c q`.

* The unique profit-maximizing quantity is `q_m = (a - c) / (2 b)`, with price
  `(a + c) / 2`.
* The efficient (competitive, price = marginal cost) quantity is
  `q_c = (a - c) / b`, and `0 < q_m < q_c`.
* The deadweight loss, the lost gains from trade `∫_{q_m}^{q_c} (P q - c) dq`
  (Atlas `DeadweightLoss.deadweightLoss` with constant marginal cost as the supply
  schedule), equals the triangle `(a - c)² / (8 b)`.
-/

@[expose] public section

namespace MathlibExt.Economics.LinearMonopoly

open MathlibExt.Economics.DeadweightLoss

/-- A monopoly with linear inverse demand `a - b q` and constant marginal cost
`c`, in the interior regime `c < a`. -/
structure Model where
  /-- Demand intercept (choke price). -/
  a : ℝ
  /-- Demand slope (magnitude). -/
  b : ℝ
  /-- Constant marginal cost. -/
  c : ℝ
  b_pos : 0 < b
  c_lt_a : c < a

/-- Inverse demand `P q = a - b q`. -/
def inverseDemand (m : Model) (q : ℝ) : ℝ := m.a - m.b * q

/-- Monopoly profit `(a - b q) q - c q`. -/
def profit (m : Model) (q : ℝ) : ℝ := inverseDemand m q * q - m.c * q

/-- Monopoly quantity `(a - c) / (2 b)`. -/
noncomputable def monopolyQuantity (m : Model) : ℝ := (m.a - m.c) / (2 * m.b)

/-- Efficient (competitive) quantity `(a - c) / b`, where price equals marginal
cost. -/
noncomputable def competitiveQuantity (m : Model) : ℝ := (m.a - m.c) / m.b

/-- The profit gap to the monopoly quantity is a scaled square. -/
theorem profit_gap_eq (m : Model) (q : ℝ) :
    profit m (monopolyQuantity m) - profit m q
      = m.b * (q - monopolyQuantity m) ^ 2 := by
  have hb : m.b ≠ 0 := ne_of_gt m.b_pos
  unfold profit inverseDemand monopolyQuantity
  field_simp
  ring

/-- The monopoly quantity maximizes profit. -/
theorem profit_le_profit_monopolyQuantity (m : Model) (q : ℝ) :
    profit m q ≤ profit m (monopolyQuantity m) := by
  have h := profit_gap_eq m q
  have hnn : (0:ℝ) ≤ m.b * (q - monopolyQuantity m) ^ 2 :=
    mul_nonneg (le_of_lt m.b_pos) (sq_nonneg _)
  linarith

/-- The monopoly quantity is the unique profit maximizer. -/
theorem eq_monopolyQuantity_of_forall_profit_le (m : Model) {q : ℝ}
    (hq : ∀ q', profit m q' ≤ profit m q) : q = monopolyQuantity m := by
  have h1 := hq (monopolyQuantity m)
  have h2 := profit_le_profit_monopolyQuantity m q
  have heq : profit m (monopolyQuantity m) = profit m q := le_antisymm h1 h2
  have h := profit_gap_eq m q
  have hb : m.b ≠ 0 := ne_of_gt m.b_pos
  have hsq : (q - monopolyQuantity m) ^ 2 = 0 := by
    have h0 : m.b * (q - monopolyQuantity m) ^ 2 = 0 := by linarith
    exact (mul_eq_zero.mp h0).resolve_left hb
  have hdiff : q - monopolyQuantity m = 0 := sq_eq_zero_iff.mp hsq
  linarith

/-- The monopoly price is `(a + c) / 2`. -/
theorem inverseDemand_monopolyQuantity (m : Model) :
    inverseDemand m (monopolyQuantity m) = (m.a + m.c) / 2 := by
  have hb : m.b ≠ 0 := ne_of_gt m.b_pos
  unfold inverseDemand monopolyQuantity
  field_simp
  ring

/-- The competitive quantity prices at marginal cost. -/
theorem inverseDemand_competitiveQuantity (m : Model) :
    inverseDemand m (competitiveQuantity m) = m.c := by
  have hb : m.b ≠ 0 := ne_of_gt m.b_pos
  unfold inverseDemand competitiveQuantity
  field_simp
  ring

/-- In the interior regime the monopoly trades a positive quantity, strictly less
than the efficient quantity. -/
theorem monopolyQuantity_mem_Ioo (m : Model) :
    monopolyQuantity m ∈ Set.Ioo 0 (competitiveQuantity m) := by
  have hb : m.b ≠ 0 := ne_of_gt m.b_pos
  have hca : 0 < m.a - m.c := sub_pos.mpr m.c_lt_a
  have h2 : (0:ℝ) < 2 := by norm_num
  have h2b : (0:ℝ) < 2 * m.b := mul_pos h2 m.b_pos
  unfold monopolyQuantity competitiveQuantity
  refine ⟨div_pos hca h2b, ?_⟩
  have hhalf : (m.a - m.c) / (2 * m.b) = (m.a - m.c) / m.b / 2 := by
    field_simp
  rw [hhalf]
  have hqc : (0:ℝ) < (m.a - m.c) / m.b := div_pos hca m.b_pos
  linarith

/-- **Monopoly deadweight loss.** The lost gains from trade between the monopoly
and the efficient quantity are the triangle `(a - c)² / (8 b)`. -/
theorem deadweightLoss_monopoly (m : Model) :
    deadweightLoss (inverseDemand m) (fun _ => m.c) (competitiveQuantity m)
        (monopolyQuantity m) = (m.a - m.c) ^ 2 / (8 * m.b) := by
  have hb : m.b ≠ 0 := ne_of_gt m.b_pos
  have hK : IntervalIntegrable (fun _ : ℝ => m.a - m.c) MeasureTheory.volume
      (monopolyQuantity m) (competitiveQuantity m) :=
    intervalIntegrable_const
  have hg : IntervalIntegrable (fun x : ℝ => m.b * x) MeasureTheory.volume
      (monopolyQuantity m) (competitiveQuantity m) :=
    (continuous_const.mul continuous_id').intervalIntegrable _ _
  unfold deadweightLoss inverseDemand
  change (∫ x in monopolyQuantity m..competitiveQuantity m,
    ((m.a - m.b * x) - m.c)) = (m.a - m.c) ^ 2 / (8 * m.b)
  have hcongr : (fun x : ℝ => (m.a - m.b * x) - m.c)
      = (fun x => (m.a - m.c) - m.b * x) := by
    funext x; ring
  rw [hcongr]
  have hsub : (∫ x in monopolyQuantity m..competitiveQuantity m,
      ((m.a - m.c) - m.b * x))
      = (∫ x in monopolyQuantity m..competitiveQuantity m, (m.a - m.c))
        - ∫ x in monopolyQuantity m..competitiveQuantity m, (m.b * x) :=
    intervalIntegral.integral_sub hK hg
  rw [hsub, intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_id, smul_eq_mul]
  unfold competitiveQuantity monopolyQuantity
  field_simp
  ring

end MathlibExt.Economics.LinearMonopoly
