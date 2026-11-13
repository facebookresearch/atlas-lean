/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import MathlibExt.InformationTheory.FiniteEntropy
import MathlibExt.InformationTheory.Pinsker

@[expose] public section

/-! # Pinsker's inequality for PMFs

For probability mass functions on a finite discrete type, the
squared `L1` distance is at most twice the KL divergence. The
right side is in `ℝ≥0∞`, so the statement stays correct when the
divergence is infinite; a `toReal` version would be false there.
The discreteness hypothesis is essential: with a coarse
sigma-algebra the two measures can coincide while the `L1`
distance is positive. This is roadmap package QCI-30 of the Atlas
TCS canon roadmap.

Source: Tsybakov, Introduction to Nonparametric Estimation
(2009), Section 2.3.
-/

open Finset
open scoped MeasureTheory

namespace InformationTheory

/-- Pinsker's inequality for probability mass functions on a finite
type, with no positivity hypotheses: the squared `L1` distance is at
most twice the Kullback-Leibler divergence (in nats). The right side
is stated in `ℝ≥0∞`, so it stays correct when the divergence is
infinite (the `ENNReal.toReal` form would be false there). -/
theorem pinsker_pmf {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p q : PMF α) :
    ENNReal.ofReal ((∑ a, |(p a).toReal - (q a).toReal|) ^ 2) ≤
      2 * InformationTheory.klDiv p.toMeasure q.toMeasure := by
  by_cases hac : p.toMeasure ≪ q.toMeasure
  · have hpq : ∀ a, q a = 0 → p a = 0 := by
      intro a hqa
      have h1 : q.toMeasure {a} = 0 := by
        rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
        exact hqa
      have h2 : p.toMeasure {a} = 0 := hac h1
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at h2
      exact h2
    have hKLreal : (InformationTheory.klDiv p.toMeasure q.toMeasure).toReal
        = ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal) :=
      InformationTheory.toReal_klDiv_toMeasure hpq
    have hx_nn : ∀ a, 0 ≤ (p a).toReal := fun a => ENNReal.toReal_nonneg
    have hy_nn : ∀ a, 0 ≤ (q a).toReal := fun a => ENNReal.toReal_nonneg
    have hsumx : (∑ a, (p a).toReal) = 1 := by
      have h := PMF.tsum_coe p
      rw [tsum_fintype] at h
      have h2 : (∑ a, p a).toReal = (1:ENNReal).toReal := by rw [h]
      rw [ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a)] at h2
      rw [ENNReal.toReal_one] at h2
      exact h2
    have hsumy : (∑ a, (q a).toReal) = 1 := by
      have h := PMF.tsum_coe q
      rw [tsum_fintype] at h
      have h2 : (∑ a, q a).toReal = (1:ENNReal).toReal := by rw [h]
      rw [ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top q a)] at h2
      rw [ENNReal.toReal_one] at h2
      exact h2
    have hac' : ∀ a, (q a).toReal = 0 → (p a).toReal = 0 := by
      intro a hqa
      have hq0 : q a = 0 := by
        by_contra hne
        have hpos : 0 < (q a).toReal :=
          ENNReal.toReal_pos hne (PMF.apply_ne_top q a)
        rw [hqa] at hpos
        exact absurd hpos (lt_irrefl 0)
      rw [hpq a hq0, ENNReal.toReal_zero]
    have hreal : (∑ a, |(p a).toReal - (q a).toReal|) ^ 2
        ≤ 2 * ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal) :=
      MathlibExt.InformationTheory.Pinsker.csiszar_kullback_pinsker_of_support
        _ _ hx_nn hy_nn hsumx hsumy hac'
    by_cases h_int :
      MeasureTheory.Integrable (MeasureTheory.llr p.toMeasure q.toMeasure)
        p.toMeasure
    · have hkl : InformationTheory.klDiv p.toMeasure q.toMeasure
          = ENNReal.ofReal
            (∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)) := by
        rw [← ENNReal.ofReal_toReal (InformationTheory.klDiv_ne_top hac h_int),
          hKLreal]
      rw [hkl]
      have h2E : (2:ENNReal) = ENNReal.ofReal 2 := by simp
      have h2nn : (0:ℝ) ≤ 2 := by norm_num
      rw [h2E, ← ENNReal.ofReal_mul h2nn]
      exact ENNReal.ofReal_le_ofReal hreal
    · rw [InformationTheory.klDiv_of_not_integrable h_int,
        ENNReal.mul_top (by simp : (2:ENNReal) ≠ 0)]
      exact le_top
  · rw [InformationTheory.klDiv_of_not_ac hac,
      ENNReal.mul_top (by simp : (2:ENNReal) ≠ 0)]
    exact le_top

end InformationTheory
