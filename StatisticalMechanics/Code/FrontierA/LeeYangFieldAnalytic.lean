/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.LeeYangZeroFree

open scoped BigOperators
open Finset

namespace StatMech.FrontierA

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def leeYangComplexFieldMagnetizationNumerator
    (beta : ℝ) (h : ℂ) : ℂ :=
  ∑ s : ConfigSpace V,
    ((beta : ℂ) * (∑ v : V, spin s v)) *
      Complex.exp
        ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
          (beta : ℂ) * h * (∑ v : V, spin s v))

theorem leeYangComplexFieldPartition_hasDerivAt
    (beta : ℝ) (h : ℂ) :
    HasDerivAt (leeYangComplexFieldPartition G beta)
      (leeYangComplexFieldMagnetizationNumerator G beta h) h := by
  unfold leeYangComplexFieldPartition
  unfold leeYangComplexFieldMagnetizationNumerator
  apply HasDerivAt.fun_sum
  intro s hs
  have hinner : HasDerivAt
      (fun y : ℂ =>
        (beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
          (beta : ℂ) * y * (∑ v : V, spin s v))
      ((beta : ℂ) * (∑ v : V, spin s v)) h := by
    convert ((hasDerivAt_const h
      ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e))).add
        (((hasDerivAt_id h).const_mul (beta : ℂ)).mul_const
          (∑ v : V, spin s v))) using 1
    · funext y
      simp only [Pi.add_apply, id_eq]
      push_cast
      rfl
    · simp only [zero_add, mul_one]
      push_cast
      rfl
  convert hinner.cexp using 1
  ring

theorem leeYangComplexFieldPartition_analyticOnNhd (beta : ℝ) :
    AnalyticOnNhd ℂ (leeYangComplexFieldPartition G beta) Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro h hh
  exact (leeYangComplexFieldPartition_hasDerivAt G beta h).differentiableAt.differentiableWithinAt

theorem leeYangComplexFieldMagnetizationNumerator_eq_deriv
    (beta : ℝ) (h : ℂ) :
    leeYangComplexFieldMagnetizationNumerator G beta h =
      deriv (leeYangComplexFieldPartition G beta) h := by
  exact (leeYangComplexFieldPartition_hasDerivAt G beta h).deriv.symm

theorem leeYangComplexFieldMagnetizationNumerator_ofReal
    (beta h : ℝ) :
    leeYangComplexFieldMagnetizationNumerator G beta (h : ℂ) =
      ((beta * ∑ s : ConfigSpace V,
        (∑ v : V, spin s v) * isingWeight G beta h s : ℝ) : ℂ) := by
  unfold leeYangComplexFieldMagnetizationNumerator
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  unfold isingWeight hamiltonian
  rw [Complex.ofReal_exp]
  rw [mul_assoc]
  congr 2
  congr 1
  push_cast
  ring

theorem leeYang_fugacity_norm_ne_one_of_re_ne_zero
    {beta : ℝ} (hbeta : 0 < beta) {h : ℂ} (hh : h.re ≠ 0) :
    ‖Complex.exp (-2 * (beta : ℂ) * h)‖ ≠ 1 := by
  rw [Complex.norm_exp]
  intro hexp
  rw [Real.exp_eq_one_iff] at hexp
  have hre : (-2 * (beta : ℂ) * h).re = -2 * beta * h.re := by
    norm_num [Complex.mul_re]
  rw [hre] at hexp
  apply hh
  nlinarith

theorem leeYangComplexFieldPartition_ne_zero_of_re_ne_zero
    {beta : ℝ} (hbeta : 0 < beta) {h : ℂ} (hh : h.re ≠ 0) :
    leeYangComplexFieldPartition G beta h ≠ 0 :=
  leeYangComplexFieldPartition_ne_zero G hbeta.le
    (leeYang_fugacity_norm_ne_one_of_re_ne_zero hbeta hh)

theorem leeYangComplexFieldPartition_zero_beta (h : ℂ) :
    leeYangComplexFieldPartition G 0 h = Fintype.card (ConfigSpace V) := by
  simp [leeYangComplexFieldPartition]

theorem leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero
    {beta : ℝ} (hbeta : 0 ≤ beta) {h : ℂ} (hh : h.re ≠ 0) :
    leeYangComplexFieldPartition G beta h ≠ 0 := by
  rcases hbeta.eq_or_lt with rfl | hbeta
  · rw [leeYangComplexFieldPartition_zero_beta]
    exact_mod_cast Fintype.card_ne_zero
  · exact leeYangComplexFieldPartition_ne_zero_of_re_ne_zero G hbeta hh

noncomputable def leeYangComplexFieldLogDerivative
    (beta : ℝ) (h : ℂ) : ℂ :=
  leeYangComplexFieldMagnetizationNumerator G beta h /
    leeYangComplexFieldPartition G beta h

theorem leeYangComplexFieldLogDerivative_eq_logDeriv
    (beta : ℝ) (h : ℂ) :
    leeYangComplexFieldLogDerivative G beta h =
      logDeriv (leeYangComplexFieldPartition G beta) h := by
  rw [logDeriv_apply]
  unfold leeYangComplexFieldLogDerivative
  rw [leeYangComplexFieldMagnetizationNumerator_eq_deriv]

theorem leeYangComplexFieldLogDerivative_ofReal
    (beta h : ℝ) :
    leeYangComplexFieldLogDerivative G beta (h : ℂ) =
      (beta : ℂ) *
        (isingExpectation G beta h (fun s => ∑ v : V, spin s v) : ℂ) := by
  rw [leeYangComplexFieldLogDerivative, leeYangComplexFieldPartition_ofReal,
    leeYangComplexFieldMagnetizationNumerator_ofReal]
  have hreal :
      (beta * ∑ s : ConfigSpace V,
          (∑ v : V, spin s v) * isingWeight G beta h s) /
          isingZ G beta h =
        beta * isingExpectation G beta h (fun s => ∑ v : V, spin s v) := by
    unfold isingExpectation isingProb
    calc
      (beta * ∑ s : ConfigSpace V,
          (∑ v : V, spin s v) * isingWeight G beta h s) /
          isingZ G beta h =
          ∑ s : ConfigSpace V,
            beta * ((∑ v : V, spin s v) * isingWeight G beta h s) /
              isingZ G beta h := by
        rw [Finset.mul_sum, Finset.sum_div]
      _ = ∑ s : ConfigSpace V,
          beta * (isingWeight G beta h s / isingZ G beta h) *
            (∑ v : V, spin s v) := by
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = beta * ∑ s : ConfigSpace V,
          isingWeight G beta h s / isingZ G beta h *
            (∑ v : V, spin s v) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
  exact_mod_cast hreal

theorem leeYangComplexFieldLogDerivative_analyticOnNhd_re_ne_zero
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangComplexFieldLogDerivative G beta)
      {h : ℂ | h.re ≠ 0} := by
  have hden := (leeYangComplexFieldPartition_analyticOnNhd G beta).mono
    (Set.subset_univ {h : ℂ | h.re ≠ 0})
  have hnum : AnalyticOnNhd ℂ
      (leeYangComplexFieldMagnetizationNumerator G beta)
      {h : ℂ | h.re ≠ 0} := by
    rw [show leeYangComplexFieldMagnetizationNumerator G beta =
        deriv (leeYangComplexFieldPartition G beta) by
      funext h
      exact leeYangComplexFieldMagnetizationNumerator_eq_deriv G beta h]
    exact (leeYangComplexFieldPartition_analyticOnNhd G beta).deriv.mono
      (Set.subset_univ _)
  exact hnum.div hden fun h hh =>
    leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero G hbeta hh

theorem leeYangComplexFieldLogDerivative_analyticOnNhd_rightHalfPlane
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangComplexFieldLogDerivative G beta)
      {h : ℂ | 0 < h.re} := by
  apply (leeYangComplexFieldLogDerivative_analyticOnNhd_re_ne_zero G hbeta).mono
  intro h hh
  exact ne_of_gt hh

theorem leeYangComplexFieldLogDerivative_analyticOnNhd_leftHalfPlane
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangComplexFieldLogDerivative G beta)
      {h : ℂ | h.re < 0} := by
  apply (leeYangComplexFieldLogDerivative_analyticOnNhd_re_ne_zero G hbeta).mono
  intro h hh
  exact ne_of_lt hh

noncomputable def leeYangComplexFieldObservableNumerator
    (beta : ℝ) (f : ConfigSpace V → ℂ) (h : ℂ) : ℂ :=
  ∑ s : ConfigSpace V, f s * Complex.exp
    ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
      (beta : ℂ) * h * (∑ v : V, spin s v))

noncomputable def leeYangComplexFieldExpectation
    (beta : ℝ) (f : ConfigSpace V → ℂ) (h : ℂ) : ℂ :=
  leeYangComplexFieldObservableNumerator G beta f h /
    leeYangComplexFieldPartition G beta h

theorem leeYangComplexFieldObservableNumerator_analyticOnNhd
    (beta : ℝ) (f : ConfigSpace V → ℂ) :
    AnalyticOnNhd ℂ
      (leeYangComplexFieldObservableNumerator G beta f) Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro h hh
  apply DifferentiableAt.differentiableWithinAt
  unfold leeYangComplexFieldObservableNumerator
  fun_prop

theorem leeYangComplexFieldExpectation_analyticOnNhd_re_ne_zero
    {beta : ℝ} (hbeta : 0 ≤ beta) (f : ConfigSpace V → ℂ) :
    AnalyticOnNhd ℂ (leeYangComplexFieldExpectation G beta f)
      {h : ℂ | h.re ≠ 0} := by
  exact ((leeYangComplexFieldObservableNumerator_analyticOnNhd G beta f).mono
      (Set.subset_univ _)).div
    ((leeYangComplexFieldPartition_analyticOnNhd G beta).mono
      (Set.subset_univ _))
    (fun h hh =>
      leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero G hbeta hh)

theorem leeYangComplexFieldExpectation_analyticOnNhd_rightHalfPlane
    {beta : ℝ} (hbeta : 0 ≤ beta) (f : ConfigSpace V → ℂ) :
    AnalyticOnNhd ℂ (leeYangComplexFieldExpectation G beta f)
      {h : ℂ | 0 < h.re} := by
  apply (leeYangComplexFieldExpectation_analyticOnNhd_re_ne_zero
    G hbeta f).mono
  intro h hh
  exact ne_of_gt hh

theorem leeYangComplexFieldExpectation_analyticOnNhd_leftHalfPlane
    {beta : ℝ} (hbeta : 0 ≤ beta) (f : ConfigSpace V → ℂ) :
    AnalyticOnNhd ℂ (leeYangComplexFieldExpectation G beta f)
      {h : ℂ | h.re < 0} := by
  apply (leeYangComplexFieldExpectation_analyticOnNhd_re_ne_zero
    G hbeta f).mono
  intro h hh
  exact ne_of_lt hh

theorem leeYangComplexFieldObservableNumerator_ofReal
    (beta h : ℝ) (f : ConfigSpace V → ℝ) :
    leeYangComplexFieldObservableNumerator G beta (fun s => (f s : ℂ)) (h : ℂ) =
      ((∑ s : ConfigSpace V, f s * isingWeight G beta h s : ℝ) : ℂ) := by
  unfold leeYangComplexFieldObservableNumerator
  push_cast
  apply Finset.sum_congr rfl
  intro s hs
  unfold isingWeight hamiltonian
  rw [Complex.ofReal_exp, mul_assoc]
  congr 2
  push_cast
  ring

theorem leeYangComplexFieldExpectation_ofReal
    (beta h : ℝ) (f : ConfigSpace V → ℝ) :
    leeYangComplexFieldExpectation G beta (fun s => (f s : ℂ)) (h : ℂ) =
      (isingExpectation G beta h f : ℂ) := by
  rw [leeYangComplexFieldExpectation,
    leeYangComplexFieldObservableNumerator_ofReal,
    leeYangComplexFieldPartition_ofReal]
  have hreal :
      (∑ s : ConfigSpace V, f s * isingWeight G beta h s) /
          isingZ G beta h = isingExpectation G beta h f := by
    unfold isingExpectation isingProb
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  exact_mod_cast hreal

end StatMech.FrontierA
