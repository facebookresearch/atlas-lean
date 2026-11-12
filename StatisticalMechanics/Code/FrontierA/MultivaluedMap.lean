/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Mathlib

open Finset
open scoped ENNReal BigOperators

namespace StatMech.FrontierA

variable {S T : Type*} [Fintype T]



theorem multivaluedMap_source_bound
    (R : S → T → Prop) [DecidableRel R]
    (epsilon : ℝ≥0∞) (K : ℕ)
    (sourceWeight : S → ℝ≥0∞) (targetWeight : T → ℝ≥0∞)
    (hdegree : ∀ s, K ≤ (Finset.univ.filter (R s)).card)
    (hweight : ∀ s t, R s t →
      epsilon * sourceWeight s ≤ targetWeight t)
    (s : S) :
    epsilon * K * sourceWeight s ≤
      ∑ t ∈ Finset.univ.filter (R s), targetWeight t := by
  calc
    epsilon * K * sourceWeight s = K * (epsilon * sourceWeight s) := by ring
    _ ≤ ((Finset.univ.filter (R s)).card : ℝ≥0∞) *
        (epsilon * sourceWeight s) := by
      gcongr
      exact_mod_cast hdegree s
    _ = ∑ _t ∈ Finset.univ.filter (R s),
        epsilon * sourceWeight s := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ t ∈ Finset.univ.filter (R s), targetWeight t := by
      gcongr with t ht
      exact hweight s t (Finset.mem_filter.mp ht).2

variable [Fintype S]





theorem multivaluedMap_weight_bound
    (R : S → T → Prop) [DecidableRel R]
    (epsilon : ℝ≥0∞) (K L : ℕ)
    (sourceWeight : S → ℝ≥0∞) (targetWeight : T → ℝ≥0∞)
    (hdegree : ∀ s, K ≤ (Finset.univ.filter (R s)).card)
    (hmultiplicity : ∀ t,
      (Finset.univ.filter (fun s => R s t)).card ≤ L)
    (hweight : ∀ s t, R s t →
      epsilon * sourceWeight s ≤ targetWeight t) :
    epsilon * K * (∑ s, sourceWeight s) ≤
      L * (∑ t, targetWeight t) := by
  calc
    epsilon * K * (∑ s, sourceWeight s) =
        ∑ s, epsilon * K * sourceWeight s := by
      rw [Finset.mul_sum]
    _ ≤ ∑ s, ∑ t ∈ Finset.univ.filter (R s), targetWeight t := by
      gcongr with s
      exact multivaluedMap_source_bound R epsilon K sourceWeight targetWeight
        hdegree hweight s
    _ = ∑ t, ∑ s ∈ Finset.univ.filter (fun s => R s t),
        targetWeight t := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ t, ((Finset.univ.filter (fun s => R s t)).card : ℝ≥0∞) *
        targetWeight t := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ t, L * targetWeight t := by
      gcongr with t
      exact_mod_cast hmultiplicity t
    _ = L * (∑ t, targetWeight t) := by
      rw [Finset.mul_sum]



theorem multivaluedMap_probability_bound
    (R : S → T → Prop) [DecidableRel R]
    (epsilon : ℝ≥0∞) (K L : ℕ)
    (sourceWeight : S → ℝ≥0∞) (targetWeight : T → ℝ≥0∞)
    (hdegree : ∀ s, K ≤ (Finset.univ.filter (R s)).card)
    (hmultiplicity : ∀ t,
      (Finset.univ.filter (fun s => R s t)).card ≤ L)
    (hweight : ∀ s t, R s t →
      epsilon * sourceWeight s ≤ targetWeight t)
    (htarget : (∑ t, targetWeight t) ≤ 1) :
    epsilon * K * (∑ s, sourceWeight s) ≤ L := by
  calc
    epsilon * K * (∑ s, sourceWeight s) ≤
        L * (∑ t, targetWeight t) :=
      multivaluedMap_weight_bound R epsilon K L sourceWeight targetWeight
        hdegree hmultiplicity hweight
    _ ≤ L * 1 := by gcongr
    _ = L := mul_one _

end StatMech.FrontierA
