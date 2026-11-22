/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Continuity

/-!
# Monopsony: a minimum-wage interval that raises employment (Atlas EC17.T04)

A single employer faces the linear inverse labor supply `w L = α + β L` (`β > 0`)
and earns revenue `γ L - δ L² / 2` from `L` workers, so the marginal revenue
product is `γ - δ L` (`δ ≥ 0`), with `α < γ`. Without regulation it pays the
supply wage and maximizes `γ L - δ L² / 2 - (α + β L) L`; the monopsony
employment is `L_m = (γ - α) / (δ + 2 β)` and the monopsony wage is
`w_m = α + β L_m`.

Under a minimum wage `w̄` it pays `max w̄ (α + β L)` per worker. For every
`w̄` strictly between the monopsony wage `w_m` and the marginal revenue product
at monopsony employment `γ - δ L_m`, every profit-maximizing employment level
exceeds `L_m`, and such a level exists.
-/

@[expose] public section

namespace MathlibExt.Economics.Monopsony

/-- A linear monopsony: inverse labor supply `α + β L`, marginal revenue product
`γ - δ L`. -/
structure Model where
  /-- Labor-supply intercept. -/
  α : ℝ
  /-- Labor-supply slope. -/
  β : ℝ
  /-- Marginal-revenue-product intercept. -/
  γ : ℝ
  /-- Marginal-revenue-product slope (magnitude). -/
  δ : ℝ
  β_pos : 0 < β
  δ_nonneg : 0 ≤ δ
  α_lt_γ : α < γ

/-- Revenue from `L` workers, `γ L - δ L² / 2`. -/
noncomputable def revenue (m : Model) (L : ℝ) : ℝ := m.γ * L - m.δ / 2 * L ^ 2

/-- Inverse labor supply: the wage needed to attract `L` workers. -/
def supplyWage (m : Model) (L : ℝ) : ℝ := m.α + m.β * L

/-- Unregulated monopsony profit. -/
noncomputable def profit (m : Model) (L : ℝ) : ℝ := revenue m L - supplyWage m L * L

/-- Monopsony employment `(γ - α) / (δ + 2 β)`. -/
noncomputable def monopsonyEmployment (m : Model) : ℝ := (m.γ - m.α) / (m.δ + 2 * m.β)

/-- Monopsony wage: the supply wage at monopsony employment. -/
noncomputable def monopsonyWage (m : Model) : ℝ := supplyWage m (monopsonyEmployment m)

/-- Profit under a minimum wage `w`: each worker is paid `max w (supplyWage L)`. -/
noncomputable def minWageProfit (m : Model) (w L : ℝ) : ℝ :=
  revenue m L - max w (supplyWage m L) * L

/-- `L` is a profit-maximizing employment level under minimum wage `w`. -/
def IsMinWageEmployment (m : Model) (w L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ L', 0 ≤ L' → minWageProfit m w L' ≤ minWageProfit m w L

/-- Monopsony employment maximizes unregulated profit. -/
theorem profit_le_profit_monopsonyEmployment (m : Model) (L : ℝ) :
    profit m L ≤ profit m (monopsonyEmployment m) := by
  have hβ : 0 < m.β := m.β_pos
  have hδ : 0 ≤ m.δ := m.δ_nonneg
  have hpos : 0 < m.δ + 2 * m.β := by linarith
  have hγ : m.γ - m.α = monopsonyEmployment m * (m.δ + 2 * m.β) := by
    unfold monopsonyEmployment
    exact (div_mul_cancel₀ _ (ne_of_gt hpos)).symm
  have e := mul_nonneg (show 0 ≤ m.δ / 2 + m.β by linarith)
    (sq_nonneg (monopsonyEmployment m - L))
  have hkey : (L - monopsonyEmployment m) * (m.γ - m.α)
      = (L - monopsonyEmployment m) * (monopsonyEmployment m * (m.δ + 2 * m.β)) := by
    rw [hγ]
  unfold profit revenue supplyWage
  linarith

/-- **Minimum wage raises monopsony employment.** For a minimum wage strictly
between the monopsony wage and the marginal revenue product at monopsony
employment, every profit-maximizing employment level exceeds monopsony
employment. -/
theorem monopsonyEmployment_lt_of_isMinWageEmployment (m : Model) {w L : ℝ}
    (hlo : monopsonyWage m < w) (hhi : w < m.γ - m.δ * monopsonyEmployment m)
    (hL : IsMinWageEmployment m w L) :
    monopsonyEmployment m < L := by
  have hβ : 0 < m.β := m.β_pos
  have hδ : 0 ≤ m.δ := m.δ_nonneg
  have hpos : 0 < m.δ + 2 * m.β := by linarith
  have hLm_pos : 0 < monopsonyEmployment m := by
    unfold monopsonyEmployment
    exact div_pos (by linarith [m.α_lt_γ]) hpos
  have hh : 0 < m.γ - w - m.δ * monopsonyEmployment m := by linarith
  set Ls : ℝ := (w - m.α) / m.β with hLs_def
  have hLs : monopsonyEmployment m < Ls := by
    rw [hLs_def, lt_div_iff₀ hβ]
    unfold monopsonyWage supplyWage at hlo
    linarith
  have hLsLm : 0 < Ls - monopsonyEmployment m := sub_pos.mpr hLs
  have hδ1 : 0 < m.δ + 1 := by linarith
  have ht1 : 0 < (Ls - monopsonyEmployment m) / 2 := by linarith
  have ht2 : 0 < (m.γ - w - m.δ * monopsonyEmployment m) / (m.δ + 1) :=
    div_pos hh hδ1
  set t : ℝ := min ((Ls - monopsonyEmployment m) / 2)
    ((m.γ - w - m.δ * monopsonyEmployment m) / (m.δ + 1)) with ht_def
  have ht_pos : 0 < t := by
    rw [ht_def]
    exact lt_min ht1 ht2
  have ht_le1 : t ≤ (Ls - monopsonyEmployment m) / 2 := by
    rw [ht_def]
    exact min_le_left _ _
  have ht_le2 : t ≤ (m.γ - w - m.δ * monopsonyEmployment m) / (m.δ + 1) := by
    rw [ht_def]
    exact min_le_right _ _
  have hkey : m.δ / 2 * t < m.γ - w - m.δ * monopsonyEmployment m := by
    have h1 : m.δ / 2 * t
        ≤ m.δ / 2 * ((m.γ - w - m.δ * monopsonyEmployment m) / (m.δ + 1)) :=
      mul_le_mul_of_nonneg_left ht_le2 (by linarith)
    have hH : 0 < (m.γ - w - m.δ * monopsonyEmployment m) * (m.δ / 2 + 1) :=
      mul_pos hh (by linarith)
    have heq : m.δ / 2 * ((m.γ - w - m.δ * monopsonyEmployment m) / (m.δ + 1))
        = (m.δ / 2 * (m.γ - w - m.δ * monopsonyEmployment m)) / (m.δ + 1) := by
      ring
    have h2 : m.δ / 2 * ((m.γ - w - m.δ * monopsonyEmployment m) / (m.δ + 1))
        < m.γ - w - m.δ * monopsonyEmployment m := by
      rw [heq, div_lt_iff₀ hδ1]
      linarith
    linarith
  set Lp : ℝ := monopsonyEmployment m + t with hLp_def
  have hLp_gt : monopsonyEmployment m < Lp := by
    rw [hLp_def]
    linarith
  have hLp_Ls : Lp < Ls := by
    have hLt : t < Ls - monopsonyEmployment m := by linarith
    rw [hLp_def]
    linarith
  have hLp_nonneg : 0 ≤ Lp := le_trans (le_of_lt hLm_pos) (le_of_lt hLp_gt)
  have hβne : m.β ≠ 0 := ne_of_gt hβ
  have hβLs : m.β * Ls = w - m.α := by
    rw [hLs_def]
    field_simp
  have hsupply_Lp : supplyWage m Lp < w := by
    have hmul : m.β * Lp < m.β * Ls := mul_lt_mul_of_pos_left hLp_Ls hβ
    unfold supplyWage
    linarith
  have hmax_Lp : max w (supplyWage m Lp) = w := max_eq_left (le_of_lt hsupply_Lp)
  by_contra hcon
  have hle : L ≤ monopsonyEmployment m := le_of_not_gt hcon
  obtain ⟨hLnonneg, hLmax⟩ := hL
  have hstep1 : minWageProfit m w L ≤ revenue m L - w * L := by
    unfold minWageProfit
    have hle' : w * L ≤ max w (supplyWage m L) * L :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hLnonneg
    linarith
  have hstep2 : revenue m L - w * L
      ≤ revenue m (monopsonyEmployment m) - w * monopsonyEmployment m := by
    have e1 := mul_nonneg (le_of_lt hh) (sub_nonneg.mpr hle)
    have e2 := mul_nonneg hδ (sq_nonneg (monopsonyEmployment m - L))
    unfold revenue
    linarith
  have hstep3 : revenue m (monopsonyEmployment m) - w * monopsonyEmployment m
      < revenue m Lp - w * Lp := by
    have hteq : Lp - monopsonyEmployment m = t := by
      rw [hLp_def]
      ring
    have e3 : 0 < (Lp - monopsonyEmployment m)
        * ((m.γ - w - m.δ * monopsonyEmployment m)
          - m.δ / 2 * (Lp - monopsonyEmployment m)) := by
      rw [hteq]
      exact mul_pos ht_pos (sub_pos.mpr hkey)
    unfold revenue
    linarith
  have hstep4 : minWageProfit m w Lp = revenue m Lp - w * Lp := by
    unfold minWageProfit
    rw [hmax_Lp]
  have hlt : minWageProfit m w L < minWageProfit m w Lp := by
    linarith
  have hle'' : minWageProfit m w Lp ≤ minWageProfit m w L := hLmax Lp hLp_nonneg
  linarith

/-- Above the monopsony wage, a profit-maximizing employment level exists. -/
theorem exists_isMinWageEmployment (m : Model) {w : ℝ}
    (hlo : monopsonyWage m < w) :
    ∃ L, IsMinWageEmployment m w L := by
  have hβ : 0 < m.β := m.β_pos
  have hδ : 0 ≤ m.δ := m.δ_nonneg
  have hpos : 0 < m.δ + 2 * m.β := by linarith
  have hβne : m.β ≠ 0 := ne_of_gt hβ
  have hLm_pos : 0 < monopsonyEmployment m := by
    unfold monopsonyEmployment
    exact div_pos (by linarith [m.α_lt_γ]) hpos
  set Ls : ℝ := (w - m.α) / m.β with hLs_def
  have hLs : monopsonyEmployment m < Ls := by
    rw [hLs_def, lt_div_iff₀ hβ]
    unfold monopsonyWage supplyWage at hlo
    linarith
  have hLs_nonneg : 0 ≤ Ls := le_trans (le_of_lt hLm_pos) (le_of_lt hLs)
  have hβLs : m.β * Ls = w - m.α := by
    rw [hLs_def]
    field_simp
  have hsupply_le : ∀ L : ℝ, supplyWage m L ≤ w ↔ L ≤ Ls := by
    intro L
    unfold supplyWage
    constructor
    · intro h
      have h1 : m.β * L ≤ m.β * Ls := by linarith
      exact le_of_mul_le_mul_left h1 hβ
    · intro h
      have h1 : m.β * L ≤ m.β * Ls := mul_le_mul_of_nonneg_left h (le_of_lt hβ)
      linarith
  have hsupply_ge : ∀ L : ℝ, Ls ≤ L → w ≤ supplyWage m L := by
    intro L hL
    unfold supplyWage
    have h1 : m.β * Ls ≤ m.β * L := mul_le_mul_of_nonneg_left hL (le_of_lt hβ)
    linarith
  have hMW_le : ∀ L : ℝ, L ≤ Ls → minWageProfit m w L = revenue m L - w * L := by
    intro L hL
    unfold minWageProfit
    rw [max_eq_left ((hsupply_le L).mpr hL)]
  have hMW_ge : ∀ L : ℝ, Ls ≤ L → minWageProfit m w L = profit m L := by
    intro L hL
    unfold minWageProfit profit
    rw [max_eq_right (hsupply_ge L hL)]
  have hγ : m.γ - m.α = monopsonyEmployment m * (m.δ + 2 * m.β) := by
    unfold monopsonyEmployment
    exact (div_mul_cancel₀ _ (ne_of_gt hpos)).symm
  have hprofit_decr : ∀ a b : ℝ, monopsonyEmployment m ≤ a → a ≤ b →
      profit m b ≤ profit m a := by
    intro a b ha hab
    have e1 := mul_nonneg (sub_nonneg.mpr hab)
      (mul_nonneg (show 0 ≤ m.δ / 2 + m.β by linarith)
        (show 0 ≤ a + b - 2 * monopsonyEmployment m by linarith))
    have hkey : (b - a) * (m.γ - m.α)
        = (b - a) * (monopsonyEmployment m * (m.δ + 2 * m.β)) := by
      rw [hγ]
    unfold profit revenue supplyWage
    linarith
  have hcont : ContinuousOn (fun L => revenue m L - w * L) (Set.Icc 0 Ls) := by
    apply Continuous.continuousOn
    unfold revenue
    continuity
  have hcompact : IsCompact (Set.Icc 0 Ls) := isCompact_Icc
  have hne : (Set.Icc 0 Ls).Nonempty :=
    ⟨0, Set.left_mem_Icc.mpr hLs_nonneg⟩
  obtain ⟨Lstar, hLstar_mem, hLstar_max⟩ := hcompact.exists_isMaxOn hne hcont
  have hLstar_le : Lstar ≤ Ls := (Set.mem_Icc.mp hLstar_mem).2
  have hLstar_nonneg : 0 ≤ Lstar := (Set.mem_Icc.mp hLstar_mem).1
  refine ⟨Lstar, hLstar_nonneg, ?_⟩
  intro L' hL'nonneg
  rw [hMW_le Lstar hLstar_le]
  by_cases hle : L' ≤ Ls
  · rw [hMW_le L' hle]
    exact hLstar_max (Set.mem_Icc.mpr ⟨hL'nonneg, hle⟩)
  · have hge : Ls ≤ L' := le_of_not_ge hle
    rw [hMW_ge L' hge]
    have h1 : profit m L' ≤ profit m Ls :=
      hprofit_decr Ls L' (le_of_lt hLs) hge
    have h2 : profit m Ls = revenue m Ls - w * Ls := by
      rw [← hMW_ge Ls le_rfl]
      exact hMW_le Ls le_rfl
    have h3 : revenue m Ls - w * Ls ≤ revenue m Lstar - w * Lstar :=
      hLstar_max (Set.mem_Icc.mpr ⟨hLs_nonneg, le_rfl⟩)
    linarith

end MathlibExt.Economics.Monopsony
