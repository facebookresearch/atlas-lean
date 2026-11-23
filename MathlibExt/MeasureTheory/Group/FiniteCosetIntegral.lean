/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The averaging statement is adapted from
`Theorems/Thm_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup.lean`
and its paired solution in `P2M/Sol/` in
https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE credits Mathlib and its respective authors under Apache 2.0.
This proof instead uses quotient pushforward and Mathlib's finite integral.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Averaging over finitely many open cosets

A function on the finite left-coset space of an open subgroup needs no
measurability assumption: its lift is constant on a finite clopen partition.
Under a left-invariant probability measure, its integral is the average
of its values on that coset space. The subgroup need not be normal.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {K : Type*} [Group K] [TopologicalSpace K]
  [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
  (H : Subgroup K) (hH : IsOpen (H : Set K))

include hH

private lemma measure_subgroup_eq_inv_index [Finite (K ⧸ H)] :
    μ (H : Set K) = (H.index : ℝ≥0∞)⁻¹ := by
  let : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h := Subgroup.index_mul_measure H hH.measurableSet μ
  rw [measure_univ] at h
  have hn : H.index ≠ 0 := Subgroup.finiteIndex_iff.mp inferInstance
  simpa only [one_div] using
    (ENNReal.eq_div_iff (by exact_mod_cast hn)
      (ENNReal.natCast_ne_top H.index)).mpr h

/-- A function on a finite left-coset space integrates to its uniform average.
No measurability of `f` or normality of `H` is required. -/
theorem integral_quotientGroup_mk [Fintype (K ⧸ H)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : K ⧸ H → E) :
    ∫ x : K, f (QuotientGroup.mk x) ∂μ =
      (H.index : ℝ)⁻¹ • ∑ q, f q := by
  classical
  let : DiscreteTopology (K ⧸ H) := QuotientGroup.discreteTopology hH
  let : MeasurableSpace (K ⧸ H) := borel _
  let : BorelSpace (K ⧸ H) := ⟨rfl⟩
  have hm : Measurable (QuotientGroup.mk : K → K ⧸ H) :=
    QuotientGroup.continuous_mk.measurable
  have hf : Integrable f (μ.map (QuotientGroup.mk : K → K ⧸ H)) :=
    Integrable.of_finite
  have hmass (q : K ⧸ H) :
      (μ.map (QuotientGroup.mk : K → K ⧸ H)).real {q} =
        (H.index : ℝ)⁻¹ := by
    rw [measureReal_def, Measure.map_apply hm (measurableSet_singleton q)]
    have hset : (QuotientGroup.mk : K → K ⧸ H) ⁻¹' {q} =
        (fun x => q.out⁻¹ * x) ⁻¹' (H : Set K) := by
      ext x
      change QuotientGroup.mk x = q ↔ q.out⁻¹ * x ∈ H
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', eq_comm]
    rw [hset, measure_preimage_mul, measure_subgroup_eq_inv_index μ H hH,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable,
    integral_fintype hf]
  simp_rw [hmass]
  exact (Finset.smul_sum ..).symm

end MeasureTheory
