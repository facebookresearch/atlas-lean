/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact source statement and representative construction below are adapted
from `Theorems/Thm_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup.lean`
and `P2M/Sol/S_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE credits Mathlib and its respective authors under Apache 2.0.
-/

import MathlibExt.MeasureTheory.Group.FiniteCosetIntegral

open MeasureTheory
open scoped BigOperators

namespace FiniteCosetIntegralTest

/-- The full original source type, with the transversal chosen before `h`. -/
theorem sourceStatement
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (H : Subgroup K) (hH : IsOpen (H : Set K)) :
    ∃ (n : ℕ) (r : Fin n → K), H.index = n ∧ 0 < n ∧
      (∀ v : K, ∃ i, (r i)⁻¹ * v ∈ H) ∧
      (∀ i j, (r i)⁻¹ * r j ∈ H → i = j) ∧
      ∀ h : K → ℂ, (∀ v : K, ∀ w ∈ H, h (v * w) = h v) →
        ∫ v, h v ∂μ = (n : ℂ)⁻¹ * ∑ i, h (r i) := by
  classical
  let : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  let : Fintype (K ⧸ H) := Fintype.ofFinite _
  let n := Fintype.card (K ⧸ H)
  let e : Fin n ≃ K ⧸ H := (Fintype.equivFin _).symm
  let r : Fin n → K := fun i => (e i).out
  have hr (i) : (QuotientGroup.mk (r i) : K ⧸ H) = e i :=
    QuotientGroup.out_eq' (e i)
  have hidx : H.index = n := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  refine ⟨n, r, hidx, Fintype.card_pos, ?_, ?_, ?_⟩
  · intro v
    refine ⟨e.symm (QuotientGroup.mk v), ?_⟩
    rw [← QuotientGroup.eq, hr, e.apply_symm_apply]
  · intro i j hij
    apply e.injective
    rw [← hr, ← hr]
    exact QuotientGroup.eq.mpr hij
  · intro h hh
    have hfactor (v : K) : h (QuotientGroup.mk v : K ⧸ H).out = h v := by
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul H v
      rw [hw, hh v w w.property]
    have havg := integral_quotientGroup_mk μ H hH (fun q : K ⧸ H => h q.out)
    simp_rw [hfactor] at havg
    rw [← e.sum_comp (fun q : K ⧸ H => h q.out)] at havg
    simpa only [hidx, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_natCast] using havg

section Consumers

variable {K : Type*} [Group K] [TopologicalSpace K]
  [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
  (H : Subgroup K) (hH : IsOpen (H : Set K))

include hH

/-- A union of selected cosets has probability equal to its fraction of cosets. -/
theorem cosetEventProbability [Finite (K ⧸ H)] [DecidableEq (K ⧸ H)]
    (s : Finset (K ⧸ H)) :
    ∫ x : K, (if QuotientGroup.mk x ∈ s then (1 : ℝ) else 0) ∂μ =
      (s.card : ℝ) / H.index := by
  classical
  let : Fintype (K ⧸ H) := Fintype.ofFinite _
  simpa [div_eq_mul_inv, mul_comm] using
    integral_quotientGroup_mk μ H hH
      (fun q : K ⧸ H => if q ∈ s then (1 : ℝ) else 0)

/-- Compute the first two moments simultaneously as a real vector integral. -/
theorem firstSecondMoments [Fintype (K ⧸ H)] (a : K ⧸ H → ℝ) :
    ∫ x : K, (a (QuotientGroup.mk x), a (QuotientGroup.mk x) ^ 2) ∂μ =
      ((∑ q, a q) / H.index, (∑ q, a q ^ 2) / H.index) := by
  rw [integral_quotientGroup_mk μ H hH (fun q => (a q, a q ^ 2))]
  ext <;> simp [Prod.fst_sum, Prod.snd_sum, div_eq_mul_inv, mul_comm]

end Consumers

/-- At index one the average has one term, not a zero-cardinality inverse. -/
theorem indexOneAverage {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ] (c : ℝ) :
    ∫ _ : K, c ∂μ = c := by
  classical
  let : Fintype (K ⧸ (⊤ : Subgroup K)) := Fintype.ofFinite _
  rw [integral_quotientGroup_mk μ (⊤ : Subgroup K) isOpen_univ (fun _ => c)]
  have hc : Fintype.card (K ⧸ (⊤ : Subgroup K)) = 1 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, Subgroup.index_top]
  simp [hc]

section Permutations

abbrev S3 := Equiv.Perm (Fin 3)

local instance : TopologicalSpace S3 := ⊥
local instance : DiscreteTopology S3 := ⟨rfl⟩
local instance : MeasurableSpace S3 := borel S3
local instance : BorelSpace S3 := ⟨rfl⟩

abbrev fixingZero : Subgroup S3 := MulAction.stabilizer S3 (0 : Fin 3)

/-- The stabilizer of a point in S₃ is an open, non-normal subgroup. -/
theorem nonNormalSubgroup : ¬ fixingZero.Normal := by
  intro h
  have hm : Equiv.swap (1 : Fin 3) 2 ∈ fixingZero := by decide
  have hc := h.conj_mem (Equiv.swap (1 : Fin 3) 2) hm (Equiv.swap 0 1)
  change ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 *
    (Equiv.swap 0 1)⁻¹ : S3) (0 : Fin 3)) = 0 at hc
  norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def] at hc

open scoped ENNReal

/-- The actual uniform probability measure on the six permutations. -/
noncomputable def uniformS3 : Measure S3 := (6 : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure uniformS3 := by
  constructor
  norm_num [uniformS3, Measure.smul_apply, Measure.count_univ,
    ENat.card_eq_coe_fintype_card, Fintype.card_perm, Nat.factorial]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance : uniformS3.IsMulLeftInvariant := by
  unfold uniformS3
  infer_instance

instance : uniformS3.IsHaarMeasure :=
  Measure.isHaarMeasure_of_isCompact_nonempty_interior uniformS3 Set.univ
    isCompact_univ (by simp) (by simp) (by simp)

/-- A concrete probability computation with a non-normal open subgroup. -/
theorem nonNormalAverage :
    ∫ g : S3, Set.indicator
      {(QuotientGroup.mk 1 : S3 ⧸ fixingZero)} (fun _ => (1 : ℝ))
      (QuotientGroup.mk g) ∂uniformS3 = 1 / 3 := by
  classical
  let : Fintype (S3 ⧸ fixingZero) := Fintype.ofFinite _
  have hidx : fixingZero.index = 3 := by
    simp [fixingZero, MulAction.index_stabilizer_of_transitive]
  rw [integral_quotientGroup_mk uniformS3 fixingZero (isOpen_discrete _)]
  simp [hidx, Set.indicator, one_div]

end Permutations

end FiniteCosetIntegralTest
