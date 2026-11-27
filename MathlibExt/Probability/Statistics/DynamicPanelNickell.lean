/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.PanelWithin
public import Mathlib.Probability.Moments.Variance

import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # A two-period dynamic-panel within-estimator counterexample -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace MathlibExt.Probability.Statistics

open WithinEstimator (withinVec)
open PanelWithin (groupMean_unit)

/-- The cross product after subtracting each vector's mean over the two periods. -/
noncomputable def twoPeriodWithinProduct (x y : Fin 2 → ℝ) : ℝ :=
  ∑ t, withinVec (fun _ : Fin 2 => ()) x t * withinVec (fun _ : Fin 2 => ()) y t

/-- In two periods the within cross product is half the product of first differences. -/
theorem twoPeriodWithinProduct_eq (x y : Fin 2 → ℝ) :
    twoPeriodWithinProduct x y = (x 0 - x 1) * (y 0 - y 1) / 2 := by
  simp only [twoPeriodWithinProduct, withinVec, groupMean_unit, Fintype.card_fin,
    Nat.cast_ofNat, Fin.sum_univ_two]
  ring

/-- With one lag regressor, the existing within Gram matrix has one entry: the sum of
squared demeaned lags over the units and periods. -/
theorem twoPeriodWithin_gram {Ω : Type*} (x : ℕ → Ω → Fin 2 → ℝ) (N : ℕ) (ω : Ω) :
    PanelWithin.withinGram (fun i w => (Matrix.of fun t (_ : Fin 1) => x i w t)) N ω 0 0 =
      ∑ i ∈ Finset.range N, twoPeriodWithinProduct (x i ω) (x i ω) := by
  simp only [PanelWithin.withinGram, Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply,
    WithinEstimator.withinMat, Matrix.of_apply, twoPeriodWithinProduct, withinVec]

/-- For a single regressor, the canonical within estimator reduces to the within cross product
sum divided by the within sum of squares, including the value zero at a singular Gram. -/
theorem twoPeriodWithin_estimator_eq {Ω : Type*} (x y : ℕ → Ω → Fin 2 → ℝ)
    (N : ℕ) (ω : Ω) :
    PanelWithin.withinEstimator (fun i w => (Matrix.of fun t (_ : Fin 1) => x i w t)) y N ω 0 =
      (∑ i ∈ Finset.range N, twoPeriodWithinProduct (x i ω) (y i ω)) /
        (∑ i ∈ Finset.range N, twoPeriodWithinProduct (x i ω) (x i ω)) := by
  have hs :
      PanelWithin.withinScore (fun i w => (Matrix.of fun t (_ : Fin 1) => x i w t)) y N ω 0 =
        ∑ i ∈ Finset.range N, twoPeriodWithinProduct (x i ω) (y i ω) := by
    simp only [PanelWithin.withinScore, Finset.sum_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, WithinEstimator.withinMat, Matrix.of_apply,
      twoPeriodWithinProduct, withinVec]
  rw [PanelWithin.withinEstimator, Matrix.inv_subsingleton]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.diagonal_apply_eq,
    Ring.inverse_eq_inv, hs, twoPeriodWithin_gram, div_eq_mul_inv]
  exact mul_comm _ _

private theorem innovation_moments {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {e : Fin 3 → Ω → ℝ} {v : ℝ} (hLp : ∀ i, MemLp (e i) 2 P)
    (hmean : ∀ i, ∫ ω, e i ω ∂P = 0) (hvar : ∀ i, variance (e i) P = v)
    (hind : Pairwise fun i j => IndepFun (e i) (e j) P) :
    (∫ ω, (e 0 ω - e 1 ω) * (e 1 ω - e 2 ω) / 2 ∂P) = -v / 2 ∧
      (∫ ω, (e 0 ω - e 1 ω) ^ 2 / 2 ∂P) = v := by
  have hsq (i : Fin 3) : (∫ ω, e i ω ^ 2 ∂P) = v :=
    (variance_of_integral_eq_zero (hLp i).aemeasurable (hmean i)).symm.trans (hvar i)
  have hcross {i j : Fin 3} (hij : i ≠ j) : (∫ ω, e i ω * e j ω ∂P) = 0 := by
    rw [(hind hij).integral_fun_mul_eq_mul_integral
      (hLp i).aestronglyMeasurable (hLp j).aestronglyMeasurable, hmean i, hmean j, mul_zero]
  have hmul (i j : Fin 3) : Integrable (fun ω => e i ω * e j ω) P :=
    (hLp i).integrable_mul (hLp j)
  constructor
  · have he (ω : Ω) : (e 0 ω - e 1 ω) * (e 1 ω - e 2 ω) / 2 =
        (2 : ℝ)⁻¹ * ((e 0 ω * e 1 ω - e 0 ω * e 2 ω) - (e 1 ω ^ 2 - e 1 ω * e 2 ω)) := by
      ring
    have h := integral_sub ((hmul 0 1).sub (hmul 0 2))
      ((hLp 1).integrable_sq.sub (hmul 1 2))
    simp only [Pi.sub_apply] at h
    simp_rw [he]
    rw [integral_const_mul, h, integral_sub (hmul 0 1) (hmul 0 2),
      integral_sub (hLp 1).integrable_sq (hmul 1 2),
      hcross (by decide : (0 : Fin 3) ≠ 1), hcross (by decide : (0 : Fin 3) ≠ 2),
      hcross (by decide : (1 : Fin 3) ≠ 2), hsq 1]
    ring
  · have he (ω : Ω) : (e 0 ω - e 1 ω) ^ 2 / 2 =
        (2 : ℝ)⁻¹ * (e 0 ω ^ 2 + e 1 ω ^ 2 - 2 * (e 0 ω * e 1 ω)) := by ring
    have h := integral_sub ((hLp 0).integrable_sq.add (hLp 1).integrable_sq)
      ((hmul 0 1).const_mul 2)
    simp only [Pi.add_apply] at h
    simp_rw [he]
    rw [integral_const_mul, h, integral_add (hLp 0).integrable_sq (hLp 1).integrable_sq,
      integral_const_mul, hcross (by decide : (0 : Fin 3) ≠ 1), hsq 0, hsq 1]
    ring

/-- **Two-period dynamic-panel counterexample.** Unit `i` has three observed outcomes
`c i + ε i 0`, `c i + ε i 1`, `c i + ε i 2`, with true lag coefficient zero. Regress the
last two outcomes on their lags after demeaning within each unit. For independent units
with identically distributed innovation vectors, and centered, square-integrable,
pairwise independent innovations of common positive variance `v` within a unit,
the within lag–error moment is `-v / 2` and the within lag sum of squares has mean `v`.
The sum of squares is eventually positive almost surely, and the within slope tends to
`-1 / 2`, not zero. No independence from `c` is needed: demeaning removes it pointwise.
This is the two-period example of the moment-ratio mechanism in M. Arellano,
*Time series and panel data econometrics*, § The Nickell Bias; it is not the general
fixed-period bias formula. -/
theorem twoPeriod_dynamic_panel_nickell {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (c : ℕ → Ω → ℝ) (ε : ℕ → Ω → Fin 3 → ℝ)
    (hUnits : iIndepFun ε P) (hIdent : ∀ i, IdentDistrib (ε i) (ε 0) P P)
    (hPeriods : Pairwise fun j k => IndepFun (fun ω => ε 0 ω j) (fun ω => ε 0 ω k) P)
    (hLp : ∀ j, MemLp (fun ω => ε 0 ω j) 2 P)
    (hmean : ∀ j, ∫ ω, ε 0 ω j ∂P = 0) {v : ℝ} (hv : 0 < v)
    (hvar : ∀ j, variance (fun ω => ε 0 ω j) P = v) :
    let x := fun (i : ℕ) (ω : Ω) (t : Fin 2) => c i ω + ε i ω t.castSucc
    let y := fun (i : ℕ) (ω : Ω) (t : Fin 2) => c i ω + ε i ω t.succ
    let u := fun (i : ℕ) (ω : Ω) (t : Fin 2) => ε i ω t.succ
    let X := fun i ω => (Matrix.of fun t (_ : Fin 1) => x i ω t)
    let S := fun i ω => twoPeriodWithinProduct (x i ω) (u i ω)
    let G := fun i ω => twoPeriodWithinProduct (x i ω) (x i ω)
    (∀ i ω, twoPeriodWithinProduct (x i ω) (y i ω) = S i ω) ∧
      (∫ ω, S 0 ω ∂P) = -v / 2 ∧ (∫ ω, G 0 ω ∂P) = v ∧
      ∀ᵐ ω ∂P,
        Tendsto (fun N => PanelWithin.withinEstimator X y N ω 0) atTop (𝓝 (-(1 / 2 : ℝ))) ∧
          ∀ᶠ N in atTop, 0 < PanelWithin.withinGram X N ω 0 0 := by
  intro x y u X S G
  have hy (i : ℕ) (ω : Ω) : twoPeriodWithinProduct (x i ω) (y i ω) = S i ω := by
    simp [S, x, y, u, twoPeriodWithinProduct_eq]
  let f : (Fin 3 → ℝ) → ℝ := fun e => (e 0 - e 1) * (e 1 - e 2) / 2
  let g : (Fin 3 → ℝ) → ℝ := fun e => (e 0 - e 1) ^ 2 / 2
  have hS : S = fun i => f ∘ ε i := by
    funext i ω
    simp [S, x, u, f, twoPeriodWithinProduct_eq]
  have hG : G = fun i => g ∘ ε i := by
    funext i ω
    simp [G, x, g, twoPeriodWithinProduct_eq]
    ring
  have hfm : Measurable f := by
    unfold f
    exact ((measurable_pi_apply (0 : Fin 3)).sub (measurable_pi_apply 1)).mul
      ((measurable_pi_apply (1 : Fin 3)).sub (measurable_pi_apply 2)) |>.div_const 2
  have hgm : Measurable g := by
    unfold g
    exact (((measurable_pi_apply (0 : Fin 3)).sub (measurable_pi_apply 1)).pow_const 2).div_const 2
  have hfInt : Integrable (f ∘ ε 0) P :=
    (((hLp 0).sub (hLp 1)).integrable_mul ((hLp 1).sub (hLp 2))).div_const 2
  have hgInt : Integrable (g ∘ ε 0) P := (((hLp 0).sub (hLp 1)).integrable_sq).div_const 2
  have hm := innovation_moments hLp hmean hvar hPeriods
  have hms : (∫ ω, S 0 ω ∂P) = -v / 2 := by rw [hS]; exact hm.1
  have hmg : (∫ ω, G 0 ω ∂P) = v := by rw [hG]; exact hm.2
  have hslS : ∀ᵐ ω ∂P,
      Tendsto (fun N => (∑ i ∈ Finset.range N, S i ω) / (N : ℝ)) atTop (𝓝 (-v / 2)) := by
    rw [← hms, hS]
    exact strong_law_ae_real _ hfInt (fun _ _ hij => (hUnits.indepFun hij).comp hfm hfm)
      (fun i => (hIdent i).comp hfm)
  have hslG : ∀ᵐ ω ∂P,
      Tendsto (fun N => (∑ i ∈ Finset.range N, G i ω) / (N : ℝ)) atTop (𝓝 v) := by
    rw [← hmg, hG]
    exact strong_law_ae_real _ hgInt (fun _ _ hij => (hUnits.indepFun hij).comp hgm hgm)
      (fun i => (hIdent i).comp hgm)
  refine ⟨hy, hms, hmg, ?_⟩
  filter_upwards [hslS, hslG] with ω hsw hgw
  have hpos : ∀ᶠ N in atTop, 0 < ∑ i ∈ Finset.range N, G i ω := by
    filter_upwards [hgw.eventually_const_lt hv, eventually_gt_atTop (0 : ℕ)] with N hN hn
    have hp : 0 < (N : ℝ) := by exact_mod_cast hn
    exact (div_pos_iff_of_pos_right hp).mp hN
  have hlim : (-v / 2) / v = -(1 / 2 : ℝ) := by field_simp [hv.ne']
  have hquot := hsw.div hgw hv.ne'
  rw [hlim] at hquot
  refine ⟨hquot.congr' ?_, ?_⟩
  · filter_upwards [hpos, eventually_gt_atTop (0 : ℕ)] with N hN hn
    have hp : (N : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    change _ = PanelWithin.withinEstimator
      (fun i w => Matrix.of fun t (_ : Fin 1) => x i w t) y N ω 0
    rw [twoPeriodWithin_estimator_eq]
    simp only [Pi.div_apply, hy]
    change ((∑ i ∈ Finset.range N, S i ω) / (N : ℝ)) /
        ((∑ i ∈ Finset.range N, G i ω) / (N : ℝ)) =
      (∑ i ∈ Finset.range N, S i ω) / ∑ i ∈ Finset.range N, G i ω
    field_simp [hp, hN.ne']
  · filter_upwards [hpos] with N hN
    change 0 < PanelWithin.withinGram
      (fun i w => Matrix.of fun t (_ : Fin 1) => x i w t) N ω 0 0
    rw [twoPeriodWithin_gram]
    exact hN

end MathlibExt.Probability.Statistics
