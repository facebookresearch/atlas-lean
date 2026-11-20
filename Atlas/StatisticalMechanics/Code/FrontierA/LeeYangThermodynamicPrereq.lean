/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.LeeYangBoxPressure

open scoped BigOperators
open Filter Set Topology

namespace StatMech.FrontierA

open StatMech.Ising StatMech.FK StatMech.FrontierB StatMech.FrontierC
  StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]




theorem finiteFerromagneticLeeYang_headline {beta : ℝ} (hbeta : 0 ≤ beta) :
    (∀ z : ℂ, (leeYangComplexPolynomial G beta).eval z = 0 → ‖z‖ = 1) ∧
    (∀ z : ℂ, ‖z‖ ≠ 1 → (leeYangComplexPolynomial G beta).eval z ≠ 0) ∧
    (∀ h : ℂ, h.re ≠ 0 → leeYangComplexFieldPartition G beta h ≠ 0) ∧
    ∀ f : ConfigSpace V → ℂ,
      AnalyticOnNhd ℂ (leeYangComplexFieldExpectation G beta f)
        {h : ℂ | h.re ≠ 0} := by
  refine ⟨finiteGraph_hasLeeYangCircle G hbeta, ?_, ?_, ?_⟩
  · intro z hz
    exact leeYangComplexPolynomial_ne_zero_of_norm_ne_one G hbeta hz
  · intro h hh
    exact leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero G hbeta hh
  · intro f
    exact leeYangComplexFieldExpectation_analyticOnNhd_re_ne_zero G hbeta f

noncomputable def leeYangRightHalfPlaneDerivativeBound
    (beta : ℝ) (h : ℂ) : ℝ :=
  beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ /
    (1 - ‖Complex.exp (-2 * (beta : ℂ) * h)‖)

noncomputable def leeYangLeftHalfPlaneDerivativeBound
    (beta : ℝ) (h : ℂ) : ℝ :=
  beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ /
    (‖Complex.exp (-2 * (beta : ℂ) * h)‖ - 1)

theorem continuousOn_leeYangRightHalfPlaneDerivativeBound
    {beta : ℝ} (hbeta : 0 < beta) :
    ContinuousOn (leeYangRightHalfPlaneDerivativeBound beta)
      {h : ℂ | 0 < h.re} := by
  have hz : Continuous
      (fun h : ℂ => ‖Complex.exp (-2 * (beta : ℂ) * h)‖) := by
    fun_prop
  apply ContinuousOn.add continuousOn_const
  apply ContinuousOn.div
  · exact continuousOn_const.mul hz.continuousOn
  · exact continuousOn_const.sub hz.continuousOn
  · intro h hh
    change 0 < h.re at hh
    have hnorm : ‖Complex.exp (-2 * (beta : ℂ) * h)‖ < 1 := by
      rw [Complex.norm_exp, Real.exp_lt_one_iff]
      norm_num [Complex.mul_re]
      nlinarith
    linarith

theorem continuousOn_leeYangLeftHalfPlaneDerivativeBound
    {beta : ℝ} (hbeta : 0 < beta) :
    ContinuousOn (leeYangLeftHalfPlaneDerivativeBound beta)
      {h : ℂ | h.re < 0} := by
  have hz : Continuous
      (fun h : ℂ => ‖Complex.exp (-2 * (beta : ℂ) * h)‖) := by
    fun_prop
  apply ContinuousOn.add continuousOn_const
  apply ContinuousOn.div
  · exact continuousOn_const.mul hz.continuousOn
  · exact hz.continuousOn.sub continuousOn_const
  · intro h hh
    change h.re < 0 at hh
    have hnorm : 1 < ‖Complex.exp (-2 * (beta : ℂ) * h)‖ := by
      rw [Complex.norm_exp, Real.one_lt_exp_iff]
      norm_num [Complex.mul_re]
      nlinarith
    linarith



theorem leeYangBox_normalizedFieldLogDerivative_boundedOn_compact_rightHalfPlane
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) {K : Set ℂ}
    (hK : IsCompact K) (hKright : K ⊆ {h : ℂ | 0 < h.re}) :
    ∃ C : ℝ, ∀ (n : ℕ) (h : ℂ), h ∈ K →
      ‖leeYangNormalizedFieldLogDerivative (boxGraph d n) beta h‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_leeYangRightHalfPlaneDerivativeBound hbeta).mono hKright)
  refine ⟨C, fun n h hh => ?_⟩
  letI : Nonempty (boxVerts d n) :=
    ⟨⟨0, by intro i; simp⟩⟩
  have hright : 0 < h.re := hKright hh
  have hfinite :=
    leeYangNormalizedFieldLogDerivative_norm_le_rightHalfPlane
      (boxGraph d n) hbeta hright
  calc
    ‖leeYangNormalizedFieldLogDerivative (boxGraph d n) beta h‖ ≤
        leeYangRightHalfPlaneDerivativeBound beta h := hfinite
    _ ≤ ‖leeYangRightHalfPlaneDerivativeBound beta h‖ :=
      Real.le_norm_self _
    _ ≤ C := hC h hh



theorem leeYangBox_normalizedFieldLogDerivative_boundedOn_compact_leftHalfPlane
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) {K : Set ℂ}
    (hK : IsCompact K) (hKleft : K ⊆ {h : ℂ | h.re < 0}) :
    ∃ C : ℝ, ∀ (n : ℕ) (h : ℂ), h ∈ K →
      ‖leeYangNormalizedFieldLogDerivative (boxGraph d n) beta h‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_leeYangLeftHalfPlaneDerivativeBound hbeta).mono hKleft)
  refine ⟨C, fun n h hh => ?_⟩
  letI : Nonempty (boxVerts d n) :=
    ⟨⟨0, by intro i; simp⟩⟩
  have hleft : h.re < 0 := hKleft hh
  have hfinite :=
    leeYangNormalizedFieldLogDerivative_norm_le_leftHalfPlane
      (boxGraph d n) hbeta hleft
  calc
    ‖leeYangNormalizedFieldLogDerivative (boxGraph d n) beta h‖ ≤
        leeYangLeftHalfPlaneDerivativeBound beta h := hfinite
    _ ≤ ‖leeYangLeftHalfPlaneDerivativeBound beta h‖ :=
      Real.le_norm_self _
    _ ≤ C := hC h hh



theorem leeYangBox_normalizedFieldLogDerivative_normalFamilyData_rightHalfPlane
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) :
    (∀ n, DifferentiableOn ℂ
      (leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      {h : ℂ | 0 < h.re}) ∧
    ∀ (K : Set ℂ), IsCompact K → K ⊆ {h : ℂ | 0 < h.re} →
      ∃ C : ℝ, ∀ (n : ℕ) (h : ℂ), h ∈ K →
        ‖leeYangNormalizedFieldLogDerivative (boxGraph d n) beta h‖ ≤ C := by
  constructor
  · intro n
    exact ((leeYangNormalizedFieldLogDerivative_analyticOnNhd_re_ne_zero
      (boxGraph d n) hbeta.le).mono
        (fun _ hh => ne_of_gt hh)).differentiableOn
  · intro K hK hKright
    exact leeYangBox_normalizedFieldLogDerivative_boundedOn_compact_rightHalfPlane
      d hbeta hK hKright



theorem leeYangBox_normalizedFieldLogDerivative_normalFamilyData_leftHalfPlane
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) :
    (∀ n, DifferentiableOn ℂ
      (leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      {h : ℂ | h.re < 0}) ∧
    ∀ (K : Set ℂ), IsCompact K → K ⊆ {h : ℂ | h.re < 0} →
      ∃ C : ℝ, ∀ (n : ℕ) (h : ℂ), h ∈ K →
        ‖leeYangNormalizedFieldLogDerivative (boxGraph d n) beta h‖ ≤ C := by
  constructor
  · intro n
    exact ((leeYangNormalizedFieldLogDerivative_analyticOnNhd_re_ne_zero
      (boxGraph d n) hbeta.le).mono
        (fun _ hh => ne_of_lt hh)).differentiableOn
  · intro K hK hKleft
    exact leeYangBox_normalizedFieldLogDerivative_boundedOn_compact_leftHalfPlane
      d hbeta hK hKleft

end StatMech.FrontierA
