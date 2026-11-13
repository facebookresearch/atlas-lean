/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveConnectorNeighborhood









namespace StatMech.FrontierA

open scoped BigOperators

structure KWSmallAdaptiveConnectorScales
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (r : ℝ) where
  beta : ℝ
  alpha : Fin n → ℝ
  hbeta : 0 < beta
  beta_lt_quarter : beta < 1 / 4
  halpha : ∀ i, 0 < alpha i
  alpha_lt_beta : ∀ i, alpha i < beta
  hsum : ∀ i, alpha i + beta < 1
  connector : ∀ i : Fin n, KWAdaptiveConnectorData
    (alpha i * (-polygon.edgeVector (i - 1)))
    (beta * polygon.edgeVector i)
  outgoing_norm_lt : ∀ i : Fin n,
    ‖beta * polygon.edgeVector i‖ < r / 4
  incoming_norm_lt : ∀ i : Fin n,
    ‖alpha i * (-polygon.edgeVector (i - 1))‖ < r / 4

theorem KWFiniteSimplePolygon.exists_smallAdaptiveConnectorScales
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    Nonempty (KWSmallAdaptiveConnectorScales polygon r) := by
  classical
  let L : ℝ := 1 + ∑ i : Fin n, ‖polygon.edgeVector i‖
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, ‖polygon.edgeVector i‖ :=
    Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hLpos : 0 < L := by
    dsimp only [L]
    linarith
  have hedge_lt (i : Fin n) : ‖polygon.edgeVector i‖ < L := by
    have hle : ‖polygon.edgeVector i‖ ≤
        ∑ j : Fin n, ‖polygon.edgeVector j‖ :=
      Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
    dsimp only [L]
    linarith
  let beta : ℝ := min (1 / 8) (r / (8 * L))
  have hbeta : 0 < beta := by
    dsimp only [beta]
    exact lt_min (by norm_num) (div_pos hr (by positivity))
  have hbeta_quarter : beta ≤ 1 / 4 := by
    exact (min_le_left _ _).trans (by norm_num)
  have hbeta_quarter_strict : beta < 1 / 4 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hbeta_bound : beta ≤ r / (8 * L) := by
    exact min_le_right _ _
  have hout (i : Fin n) : ‖beta * polygon.edgeVector i‖ < r / 4 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbeta]
    calc
      beta * ‖polygon.edgeVector i‖ < beta * L :=
        mul_lt_mul_of_pos_left (hedge_lt i) hbeta
      _ ≤ (r / (8 * L)) * L :=
        mul_le_mul_of_nonneg_right hbeta_bound hLpos.le
      _ = r / 8 := by field_simp
      _ < r / 4 := by linarith
  obtain ⟨alpha, halpha, hconnector⟩ :=
    polygon.exists_adaptiveConnectorScales hcoords beta beta hbeta hbeta
  refine ⟨{
    beta := beta
    alpha := alpha
    hbeta := hbeta
    beta_lt_quarter := hbeta_quarter_strict
    halpha := fun i ↦ (halpha i).1
    alpha_lt_beta := fun i ↦ (halpha i).2.1
    hsum := ?_
    connector := fun i ↦ (hconnector i).some
    outgoing_norm_lt := hout
    incoming_norm_lt := ?_ }⟩
  · intro i
    have hai := (halpha i).2.1
    linarith
  · intro i
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (halpha i).1, norm_neg]
    calc
      alpha i * ‖polygon.edgeVector (i - 1)‖ ≤
          beta * ‖polygon.edgeVector (i - 1)‖ :=
        mul_le_mul_of_nonneg_right (halpha i).2.1.le (norm_nonneg _)
      _ = ‖beta * polygon.edgeVector (i - 1)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbeta]
      _ < r / 4 := hout (i - 1)

noncomputable def KWSmallAdaptiveConnectorScales.toPatchedData
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    {r : ℝ} (scales : KWSmallAdaptiveConnectorScales polygon r)
    (hM : 2 ≤ M) : KWAdaptivePatchedData (M := M) polygon where
  data := kwEndpointParameterData polygon M scales.beta scales.alpha
    (by omega) scales.hbeta scales.halpha scales.hsum
  beta := scales.beta
  alpha := scales.alpha
  hM := hM
  hbeta := scales.hbeta
  halpha := scales.halpha
  hsum := scales.hsum
  parameter_one := kwEndpointParameterData_parameter_one
    polygon scales.beta scales.alpha (by omega) scales.hbeta
      scales.halpha scales.hsum
  parameter_penultimate := kwEndpointParameterData_parameter_penultimate
    polygon scales.beta scales.alpha (by omega) scales.hbeta
      scales.halpha scales.hsum
  connector := scales.connector

end StatMech.FrontierA
