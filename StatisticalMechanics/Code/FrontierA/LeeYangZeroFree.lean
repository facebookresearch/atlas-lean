/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.LeeYangAsano
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.LogDeriv

open scoped BigOperators
open Finset Polynomial

namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def leeYangComplexFieldPartition (beta : ℝ) (h : ℂ) : ℂ :=
  ∑ s : ConfigSpace V, Complex.exp
    ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
      (beta : ℂ) * h * (∑ v : V, spin s v))



theorem leeYangComplexFieldPartition_ofReal (beta h : ℝ) :
    leeYangComplexFieldPartition G beta (h : ℂ) = (isingZ G beta h : ℂ) := by
  unfold leeYangComplexFieldPartition isingZ isingWeight hamiltonian
  change (∑ s : ConfigSpace V, Complex.exp
      ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
        (beta : ℂ) * (h : ℂ) * (∑ v : V, spin s v))) =
    (algebraMap ℝ ℂ) (∑ s : ConfigSpace V,
      Real.exp (-beta * (-(∑ e ∈ G.edgeFinset, bond s e) -
        h * ∑ v : V, spin s v)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  change Complex.exp
      ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
        (beta : ℂ) * (h : ℂ) * (∑ v : V, spin s v)) =
    (Real.exp (-beta * (-(∑ e ∈ G.edgeFinset, bond s e) -
      h * ∑ v : V, spin s v)) : ℂ)
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem leeYangComplexFieldPartition_eq_fugacity (beta : ℝ) (h : ℂ) :
    (leeYangComplexPolynomial G beta).eval (Complex.exp (-2 * (beta : ℂ) * h)) =
      Complex.exp (-(beta : ℂ) * h * Fintype.card V) *
        leeYangComplexFieldPartition G beta h := by
  rw [eval_leeYangComplexPolynomial]
  unfold leeYangComplexFieldPartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Complex.exp_nat_mul]
  unfold zeroFieldInteractionWeight
  rw [Complex.ofReal_exp]
  rw [← Complex.exp_add, ← Complex.exp_add]
  rw [sum_spin_eq_card_sub_two_mul_minusSpinCount s]
  congr 1
  push_cast
  ring

theorem leeYangComplexPolynomial_ne_zero_of_norm_ne_one
    {beta : ℝ} (hbeta : 0 ≤ beta) {z : ℂ} (hz : ‖z‖ ≠ 1) :
    (leeYangComplexPolynomial G beta).eval z ≠ 0 := by
  intro hroot
  exact hz (finiteGraph_hasLeeYangCircle G hbeta z hroot)

theorem leeYangComplexFieldPartition_ne_zero
    {beta : ℝ} (hbeta : 0 ≤ beta) {h : ℂ}
    (hfugacity : ‖Complex.exp (-2 * (beta : ℂ) * h)‖ ≠ 1) :
    leeYangComplexFieldPartition G beta h ≠ 0 := by
  intro hzero
  apply leeYangComplexPolynomial_ne_zero_of_norm_ne_one G hbeta hfugacity
  rw [leeYangComplexFieldPartition_eq_fugacity, hzero, mul_zero]



noncomputable def leeYangFugacityLogDerivative (beta : ℝ) (z : ℂ) : ℂ :=
  (leeYangComplexPolynomial G beta).derivative.eval z /
    (leeYangComplexPolynomial G beta).eval z

theorem leeYangFugacityLogDerivative_eq_logDeriv (beta : ℝ) (z : ℂ) :
    leeYangFugacityLogDerivative G beta z =
      logDeriv (fun w ↦ (leeYangComplexPolynomial G beta).eval w) z := by
  rw [logDeriv_apply]
  unfold leeYangFugacityLogDerivative
  rw [(leeYangComplexPolynomial G beta).hasDerivAt z |>.deriv]

theorem leeYangFugacityLogDerivative_analyticOnNhd_offCircle
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangFugacityLogDerivative G beta)
      {z : ℂ | ‖z‖ ≠ 1} := by
  have hnum : AnalyticOnNhd ℂ
      (fun z ↦ (leeYangComplexPolynomial G beta).derivative.eval z) Set.univ :=
    AnalyticOnNhd.eval_polynomial _
  have hden : AnalyticOnNhd ℂ
      (fun z ↦ (leeYangComplexPolynomial G beta).eval z) Set.univ :=
    AnalyticOnNhd.eval_polynomial _
  exact (hnum.mono (Set.subset_univ _)).div (hden.mono (Set.subset_univ _))
    (fun z hz ↦ leeYangComplexPolynomial_ne_zero_of_norm_ne_one G hbeta hz)

theorem leeYangFugacityLogDerivative_analyticOnNhd_openUnitDisk
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangFugacityLogDerivative G beta)
      {z : ℂ | ‖z‖ < 1} := by
  apply (leeYangFugacityLogDerivative_analyticOnNhd_offCircle G hbeta).mono
  intro z hz
  exact ne_of_lt hz

theorem leeYangFugacityLogDerivative_analyticOnNhd_exterior
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangFugacityLogDerivative G beta)
      {z : ℂ | 1 < ‖z‖} := by
  apply (leeYangFugacityLogDerivative_analyticOnNhd_offCircle G hbeta).mono
  intro z hz
  exact ne_of_gt hz

end StatMech.FrontierA
