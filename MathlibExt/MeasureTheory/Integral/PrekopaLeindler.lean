/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
open MeasureTheory

open scoped ENNReal

namespace MathlibExt.MeasureTheory.Integral.PrekopaLeindlerWanted

-- Weighted AM–GM and superadditivity for `ℝ≥0∞`, and one-dimensional
-- Brunn–Minkowski for compact sets: building blocks for Prékopa–Leindler.

private theorem ennreal_geom_mean_le_arith_mean2
    (a b : ℝ≥0∞) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    a ^ (1 - t) * b ^ t ≤ ENNReal.ofReal (1 - t) * a + ENNReal.ofReal t * b := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hpq : (1 / (1 - t)).HolderConjugate (1 / t) := by
    rw [Real.holderConjugate_iff]
    constructor
    · rw [lt_div_iff₀ h1t]; linarith
    · field_simp; ring
  have hY := ENNReal.young_inequality (a ^ (1 - t)) (b ^ t) hpq
  have e1 : ((a ^ (1 - t)) ^ (1 / (1 - t)) : ℝ≥0∞) = a := by
    rw [← ENNReal.rpow_mul]
    have : (1 - t) * (1 / (1 - t)) = 1 := by field_simp
    rw [this, ENNReal.rpow_one]
  have e2 : ((b ^ t) ^ (1 / t) : ℝ≥0∞) = b := by
    rw [← ENNReal.rpow_mul]
    have : t * (1 / t) = 1 := by field_simp
    rw [this, ENNReal.rpow_one]
  rw [e1, e2] at hY
  have d1 : (a / ENNReal.ofReal (1 / (1 - t)) : ℝ≥0∞) = ENNReal.ofReal (1 - t) * a := by
    have : ENNReal.ofReal (1 / (1 - t)) = (ENNReal.ofReal (1 - t))⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos h1t]
    rw [this, div_eq_mul_inv, inv_inv, mul_comm]
  have d2 : (b / ENNReal.ofReal (1 / t) : ℝ≥0∞) = ENNReal.ofReal t * b := by
    have : ENNReal.ofReal (1 / t) = (ENNReal.ofReal t)⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos ht0]
    rw [this, div_eq_mul_inv, inv_inv, mul_comm]
  rw [d1, d2] at hY
  exact hY

private theorem ennreal_add_rpow_mul_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (u₁ u₂ v₁ v₂ : ℝ≥0∞) :
    u₁ ^ (1 - t) * v₁ ^ t + u₂ ^ (1 - t) * v₂ ^ t ≤
      (u₁ + u₂) ^ (1 - t) * (v₁ + v₂) ^ t := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have h1t' : (0 : ℝ) ≤ 1 - t := le_of_lt h1t
  have ht0' : (0 : ℝ) ≤ t := le_of_lt ht0
  have hz1 : (0 : ℝ≥0∞) ^ (1 - t) = 0 := ENNReal.zero_rpow_of_pos h1t
  have hzt : (0 : ℝ≥0∞) ^ t = 0 := ENNReal.zero_rpow_of_pos ht0
  by_cases hA0 : u₁ + u₂ = 0
  · have hu1 : u₁ = 0 := by
      have hle : u₁ ≤ u₁ + u₂ := le_add_of_nonneg_right (by positivity)
      rw [hA0] at hle
      exact le_antisymm hle (by positivity)
    have hu2 : u₂ = 0 := by
      have hle : u₂ ≤ u₁ + u₂ := le_add_of_nonneg_left (by positivity)
      rw [hA0] at hle
      exact le_antisymm hle (by positivity)
    simp [hu1, hu2, hz1]
  by_cases hB0 : v₁ + v₂ = 0
  · have hv1 : v₁ = 0 := by
      have hle : v₁ ≤ v₁ + v₂ := le_add_of_nonneg_right (by positivity)
      rw [hB0] at hle
      exact le_antisymm hle (by positivity)
    have hv2 : v₂ = 0 := by
      have hle : v₂ ≤ v₁ + v₂ := le_add_of_nonneg_left (by positivity)
      rw [hB0] at hle
      exact le_antisymm hle (by positivity)
    simp [hv1, hv2, hzt]
  by_cases hAT : u₁ + u₂ = ⊤
  · have hBt : (v₁ + v₂) ^ t ≠ 0 := by
      intro hcon
      rcases ENNReal.rpow_eq_zero_iff.mp hcon with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact hB0 h1
      · linarith
    have hRHS : (u₁ + u₂) ^ (1 - t) * (v₁ + v₂) ^ t = ⊤ := by
      rw [hAT, ENNReal.top_rpow_of_pos h1t, ENNReal.top_mul hBt]
    rw [hRHS]
    exact le_top
  by_cases hBT : v₁ + v₂ = ⊤
  · have hAt : (u₁ + u₂) ^ (1 - t) ≠ 0 := by
      intro hcon
      rcases ENNReal.rpow_eq_zero_iff.mp hcon with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact hA0 h1
      · linarith
    have hRHS : (u₁ + u₂) ^ (1 - t) * (v₁ + v₂) ^ t = ⊤ := by
      rw [hBT, ENNReal.top_rpow_of_pos ht0, mul_comm]
      exact ENNReal.top_mul hAt
    rw [hRHS]
    exact le_top
  have hAne : (u₁ + u₂) ≠ ⊤ := hAT
  have hBne : (v₁ + v₂) ≠ ⊤ := hBT
  have hAinv : (u₁ + u₂) * (u₁ + u₂)⁻¹ = 1 := ENNReal.mul_inv_cancel hA0 hAne
  have hBinv : (v₁ + v₂) * (v₁ + v₂)⁻¹ = 1 := ENNReal.mul_inv_cancel hB0 hBne
  have hU : u₁ * (u₁ + u₂)⁻¹ + u₂ * (u₁ + u₂)⁻¹ = 1 := by
    rw [← add_mul, hAinv]
  have hV : v₁ * (v₁ + v₂)⁻¹ + v₂ * (v₁ + v₂)⁻¹ = 1 := by
    rw [← add_mul, hBinv]
  have hAu1 : (u₁ + u₂) * (u₁ * (u₁ + u₂)⁻¹) = u₁ := by
    calc (u₁ + u₂) * (u₁ * (u₁ + u₂)⁻¹)
        = ((u₁ + u₂) * (u₁ + u₂)⁻¹) * u₁ := by ring
      _ = u₁ := by rw [hAinv, one_mul]
  have hAu2 : (u₁ + u₂) * (u₂ * (u₁ + u₂)⁻¹) = u₂ := by
    calc (u₁ + u₂) * (u₂ * (u₁ + u₂)⁻¹)
        = ((u₁ + u₂) * (u₁ + u₂)⁻¹) * u₂ := by ring
      _ = u₂ := by rw [hAinv, one_mul]
  have hBv1 : (v₁ + v₂) * (v₁ * (v₁ + v₂)⁻¹) = v₁ := by
    calc (v₁ + v₂) * (v₁ * (v₁ + v₂)⁻¹)
        = ((v₁ + v₂) * (v₁ + v₂)⁻¹) * v₁ := by ring
      _ = v₁ := by rw [hBinv, one_mul]
  have hBv2 : (v₁ + v₂) * (v₂ * (v₁ + v₂)⁻¹) = v₂ := by
    calc (v₁ + v₂) * (v₂ * (v₁ + v₂)⁻¹)
        = ((v₁ + v₂) * (v₁ + v₂)⁻¹) * v₂ := by ring
      _ = v₂ := by rw [hBinv, one_mul]
  have e1 : u₁ ^ (1 - t) = (u₁ + u₂) ^ (1 - t) * (u₁ * (u₁ + u₂)⁻¹) ^ (1 - t) := by
    conv_lhs => rw [← hAu1]
    rw [ENNReal.mul_rpow_of_nonneg _ _ h1t']
  have e2 : u₂ ^ (1 - t) = (u₁ + u₂) ^ (1 - t) * (u₂ * (u₁ + u₂)⁻¹) ^ (1 - t) := by
    conv_lhs => rw [← hAu2]
    rw [ENNReal.mul_rpow_of_nonneg _ _ h1t']
  have e3 : v₁ ^ t = (v₁ + v₂) ^ t * (v₁ * (v₁ + v₂)⁻¹) ^ t := by
    conv_lhs => rw [← hBv1]
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht0']
  have e4 : v₂ ^ t = (v₁ + v₂) ^ t * (v₂ * (v₁ + v₂)⁻¹) ^ t := by
    conv_lhs => rw [← hBv2]
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht0']
  have g1 := ennreal_geom_mean_le_arith_mean2 (u₁ * (u₁ + u₂)⁻¹) (v₁ * (v₁ + v₂)⁻¹)
    ht0 ht1
  have g2 := ennreal_geom_mean_le_arith_mean2 (u₂ * (u₁ + u₂)⁻¹) (v₂ * (v₁ + v₂)⁻¹)
    ht0 ht1
  have hS : (u₁ * (u₁ + u₂)⁻¹) ^ (1 - t) * (v₁ * (v₁ + v₂)⁻¹) ^ t +
        (u₂ * (u₁ + u₂)⁻¹) ^ (1 - t) * (v₂ * (v₁ + v₂)⁻¹) ^ t ≤ 1 := by
    calc (u₁ * (u₁ + u₂)⁻¹) ^ (1 - t) * (v₁ * (v₁ + v₂)⁻¹) ^ t +
          (u₂ * (u₁ + u₂)⁻¹) ^ (1 - t) * (v₂ * (v₁ + v₂)⁻¹) ^ t
        ≤ (ENNReal.ofReal (1 - t) * (u₁ * (u₁ + u₂)⁻¹) +
            ENNReal.ofReal t * (v₁ * (v₁ + v₂)⁻¹)) +
          (ENNReal.ofReal (1 - t) * (u₂ * (u₁ + u₂)⁻¹) +
            ENNReal.ofReal t * (v₂ * (v₁ + v₂)⁻¹)) :=
          add_le_add g1 g2
      _ = ENNReal.ofReal (1 - t) * (u₁ * (u₁ + u₂)⁻¹ + u₂ * (u₁ + u₂)⁻¹) +
          ENNReal.ofReal t * (v₁ * (v₁ + v₂)⁻¹ + v₂ * (v₁ + v₂)⁻¹) := by ring
      _ = 1 := by
          rw [hU, hV, mul_one, mul_one, ← ENNReal.ofReal_add h1t' ht0']
          have hring : (1 - t) + t = 1 := by ring
          rw [hring, ENNReal.ofReal_one]
  calc u₁ ^ (1 - t) * v₁ ^ t + u₂ ^ (1 - t) * v₂ ^ t
      = (u₁ + u₂) ^ (1 - t) * (v₁ + v₂) ^ t *
        ((u₁ * (u₁ + u₂)⁻¹) ^ (1 - t) * (v₁ * (v₁ + v₂)⁻¹) ^ t +
          (u₂ * (u₁ + u₂)⁻¹) ^ (1 - t) * (v₂ * (v₁ + v₂)⁻¹) ^ t) := by
        rw [e1, e2, e3, e4]; ring
    _ ≤ (u₁ + u₂) ^ (1 - t) * (v₁ + v₂) ^ t * 1 :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (u₁ + u₂) ^ (1 - t) * (v₁ + v₂) ^ t := mul_one _

open scoped Pointwise in
private theorem compact_add_volume_le_1d {K L : Set ℝ}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    volume K + volume L ≤ volume (K + L) := by
  obtain ⟨a₁, ha₁K, ha₁⟩ := hK.exists_isMaxOn hKne continuousOn_id
  obtain ⟨b₀, hb₀L, hb₀⟩ := hL.exists_isMinOn hLne continuousOn_id
  have hAcomp : IsCompact ((fun x => x + b₀) '' K) :=
    hK.image (continuous_id.add continuous_const)
  have hBcomp : IsCompact ((fun y => a₁ + y) '' L) :=
    hL.image (continuous_const.add continuous_id)
  have hAmeas : MeasurableSet ((fun x => x + b₀) '' K) := hAcomp.measurableSet
  have hBmeas : MeasurableSet ((fun y => a₁ + y) '' L) := hBcomp.measurableSet
  have hAK : (fun x => x + b₀) '' K = (fun x => x + (-b₀)) ⁻¹' K := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hyK, rfl⟩
      have hring : (y + b₀) + (-b₀) = y := by ring
      rw [hring]
      exact hyK
    · intro hx
      refine ⟨x + (-b₀), hx, by ring⟩
  have hBK : (fun y => a₁ + y) '' L = (fun y => (-a₁) + y) ⁻¹' L := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨z, hzL, rfl⟩
      have hring : (-a₁) + (a₁ + z) = z := by ring
      rw [hring]
      exact hzL
    · intro hy
      refine ⟨(-a₁) + y, hy, by ring⟩
  have hvolA : volume ((fun x => x + b₀) '' K) = volume K := by
    rw [hAK]
    exact (measurePreserving_add_right volume (-b₀)).measure_preimage_emb
      (measurableEmbedding_addRight (-b₀)) K
  have hvolB : volume ((fun y => a₁ + y) '' L) = volume L := by
    rw [hBK]
    exact (measurePreserving_add_left volume (-a₁)).measure_preimage_emb
      (measurableEmbedding_addLeft (-a₁)) L
  have hAsub : (fun x => x + b₀) '' K ⊆ K + L := by
    rintro x ⟨y, hyK, rfl⟩
    exact Set.add_mem_add hyK hb₀L
  have hBsub : (fun y => a₁ + y) '' L ⊆ K + L := by
    rintro y ⟨z, hzL, rfl⟩
    exact Set.add_mem_add ha₁K hzL
  have hAlo : (fun x => x + b₀) '' K ⊆ Set.Iic (a₁ + b₀) := by
    rintro x ⟨y, hyK, rfl⟩
    simp only [Set.mem_Iic]
    have hle : y ≤ a₁ := ha₁ hyK
    linarith
  have hBhi : (fun y => a₁ + y) '' L ⊆ Set.Ici (a₁ + b₀) := by
    rintro y ⟨z, hzL, rfl⟩
    simp only [Set.mem_Ici]
    have hle : b₀ ≤ z := hb₀ hzL
    linarith
  have hIsub : (fun x => x + b₀) '' K ∩ (fun y => a₁ + y) '' L ⊆ {a₁ + b₀} := by
    rintro x ⟨hxA, hxB⟩
    simp only [Set.mem_singleton_iff]
    exact le_antisymm (hAlo hxA) (hBhi hxB)
  have hI : volume ((fun x => x + b₀) '' K ∩ (fun y => a₁ + y) '' L) = 0 := by
    refine le_antisymm ?_ (by positivity)
    calc volume ((fun x => x + b₀) '' K ∩ (fun y => a₁ + y) '' L)
          ≤ volume ({a₁ + b₀} : Set ℝ) := measure_mono hIsub
      _ = 0 := Real.volume_singleton
  have hdisj1 : Disjoint ((fun x => x + b₀) '' K \ (fun y => a₁ + y) '' L)
      ((fun x => x + b₀) '' K ∩ (fun y => a₁ + y) '' L) :=
    Set.disjoint_sdiff_inter
  have hdisj2 : Disjoint ((fun x => x + b₀) '' K \ (fun y => a₁ + y) '' L)
      ((fun y => a₁ + y) '' L) :=
    Set.disjoint_left.mpr fun x hxC hxB => hxC.2 hxB
  have hunion1 : (fun x => x + b₀) '' K \ (fun y => a₁ + y) '' L ∪
      (fun x => x + b₀) '' K ∩ (fun y => a₁ + y) '' L = (fun x => x + b₀) '' K :=
    Set.sdiff_union_inter _ _
  have hunion2 : (fun x => x + b₀) '' K \ (fun y => a₁ + y) '' L ∪
      (fun y => a₁ + y) '' L =
      (fun x => x + b₀) '' K ∪ (fun y => a₁ + y) '' L := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    tauto
  have hvolA' : volume ((fun x => x + b₀) '' K)
      = volume ((fun x => x + b₀) '' K \ (fun y => a₁ + y) '' L)
        + volume ((fun x => x + b₀) '' K ∩ (fun y => a₁ + y) '' L) := by
    have h := measure_union (μ := volume) hdisj1 (hAmeas.inter hBmeas)
    rw [hunion1] at h
    exact h
  have hvolU : volume ((fun x => x + b₀) '' K ∪ (fun y => a₁ + y) '' L)
      = volume ((fun x => x + b₀) '' K \ (fun y => a₁ + y) '' L)
        + volume ((fun y => a₁ + y) '' L) := by
    have h := measure_union (μ := volume) hdisj2 hBmeas
    rw [hunion2] at h
    exact h
  calc volume K + volume L
      = volume ((fun x => x + b₀) '' K \ (fun y => a₁ + y) '' L)
        + volume ((fun y => a₁ + y) '' L) := by
        rw [← hvolA, ← hvolB, hvolA', hI, add_zero]
    _ = volume ((fun x => x + b₀) '' K ∪ (fun y => a₁ + y) '' L) := hvolU.symm
    _ ≤ volume (K + L) :=
        measure_mono (Set.union_subset hAsub hBsub)

private theorem volume_image_const_mul_of_nonneg (K : Set ℝ) {c : ℝ} (hc : 0 ≤ c) :
    volume ((fun x => c * x) '' K) = ENNReal.ofReal c * volume K := by
  rcases eq_or_lt_of_le hc with rfl | hpos
  · have hsub : (fun x => (0 : ℝ) * x) '' K ⊆ {0} := by
      rintro x ⟨y, _, rfl⟩
      simp
    have hvol : volume ((fun x => (0 : ℝ) * x) '' K) = 0 :=
      le_antisymm ((measure_mono hsub).trans (le_of_eq Real.volume_singleton))
        (by positivity)
    rw [hvol, ENNReal.ofReal_zero, zero_mul]
  · have hcne : c ≠ 0 := ne_of_gt hpos
    have him : (fun x => c * x) '' K = (fun x => c⁻¹ * x) ⁻¹' K := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hyK, hyx⟩
        rw [← hyx, inv_mul_cancel_left₀ hcne y]
        exact hyK
      · intro hx
        exact ⟨c⁻¹ * x, hx, mul_inv_cancel_left₀ hcne x⟩
    rw [him, Real.volume_preimage_mul_left (inv_ne_zero hcne)]
    congr 1
    rw [inv_inv, abs_of_pos hpos]

open scoped Pointwise in
private theorem compact_brunn_minkowski_scaled {K L : Set ℝ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    ENNReal.ofReal (1 - t) * volume K + ENNReal.ofReal t * volume L ≤
      volume ((fun x => (1 - t) * x) '' K + (fun y => t * y) '' L) := by
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith
  have ht0' : (0 : ℝ) ≤ t := le_of_lt ht0
  have hK' : IsCompact ((fun x => (1 - t) * x) '' K) :=
    hK.image (continuous_const.mul continuous_id)
  have hL' : IsCompact ((fun y => t * y) '' L) :=
    hL.image (continuous_const.mul continuous_id)
  have hKne' : ((fun x => (1 - t) * x) '' K).Nonempty := hKne.image _
  have hLne' : ((fun y => t * y) '' L).Nonempty := hLne.image _
  have hbase := compact_add_volume_le_1d hK' hL' hKne' hLne'
  rw [volume_image_const_mul_of_nonneg K h1t,
    volume_image_const_mul_of_nonneg L ht0'] at hbase
  exact hbase

open scoped Pointwise in
private theorem compact_prekopa_indicator {K L : Set ℝ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    volume K ^ (1 - t) * volume L ^ t ≤
      volume ((fun x => (1 - t) * x) '' K + (fun y => t * y) '' L) := by
  refine le_trans (ennreal_geom_mean_le_arith_mean2 _ _ ht0 ht1) ?_
  exact compact_brunn_minkowski_scaled ht0 ht1 hK hL hKne hLne

private theorem volume_image_add_right (S : Set ℝ) (c : ℝ) :
    volume ((fun x => x + c) '' S) = volume S := by
  have h : (fun x => x + c) '' S = (fun x => x + (-c)) ⁻¹' S := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hyS, rfl⟩
      have hring : (y + c) + (-c) = y := by ring
      rw [hring]
      exact hyS
    · intro hx
      exact ⟨x + (-c), hx, by ring⟩
  rw [h]
  exact (measurePreserving_add_right volume (-c)).measure_preimage_emb
    (measurableEmbedding_addRight (-c)) S

private theorem volume_image_add_left (S : Set ℝ) (c : ℝ) :
    volume ((fun x => c + x) '' S) = volume S := by
  have h : (fun x => c + x) = (fun x => x + c) := by
    funext x
    exact add_comm c x
  rw [h]
  exact volume_image_add_right S c

private theorem volume_image_affine_add_right (S : Set ℝ) {a c : ℝ} (ha : 0 ≤ a) :
    volume ((fun x => a * x + c) '' S) = ENNReal.ofReal a * volume S := by
  have h : (fun x => a * x + c) '' S
      = (fun z => z + c) '' ((fun x => a * x) '' S) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hyS, rfl⟩
      exact ⟨a * y, ⟨y, hyS, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, hyS, rfl⟩, rfl⟩
      exact ⟨y, hyS, rfl⟩
  rw [h, volume_image_add_right, volume_image_const_mul_of_nonneg S ha]

private theorem volume_image_affine_add_left (S : Set ℝ) (c : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    volume ((fun x => c + a * x) '' S) = ENNReal.ofReal a * volume S := by
  have h : (fun x => c + a * x) = (fun x => a * x + c) := by
    funext x
    exact add_comm _ _
  rw [h]
  exact volume_image_affine_add_right S ha

private theorem exists_lt_add_lt {A B C t : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (hlt : C < (1 - t) * A + t * B) :
    ∃ r1 r2 : ℝ, 0 ≤ r1 ∧ r1 < A ∧ 0 ≤ r2 ∧ r2 < B ∧
      C < (1 - t) * r1 + t * r2 := by
  have hδpos : 0 < (1 - t) * A + t * B - C := by linarith
  set ε := min (A / 2) (min (B / 2) (((1 - t) * A + t * B - C) / 2)) with hεdef
  have hA2 : (0 : ℝ) < A / 2 := by linarith
  have hB2 : (0 : ℝ) < B / 2 := by linarith
  have hδ2 : (0 : ℝ) < ((1 - t) * A + t * B - C) / 2 := by linarith
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min_iff.mpr ⟨hA2, lt_min_iff.mpr ⟨hB2, hδ2⟩⟩
  have hεA : ε ≤ A / 2 := by
    rw [hεdef]
    exact min_le_left _ _
  have hεB : ε ≤ B / 2 := by
    rw [hεdef]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεδ : ε ≤ ((1 - t) * A + t * B - C) / 2 := by
    rw [hεdef]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hεδlt : ε < (1 - t) * A + t * B - C := by
    have h2 : ((1 - t) * A + t * B - C) / 2 < (1 - t) * A + t * B - C := by
      linarith
    exact lt_of_le_of_lt hεδ h2
  refine ⟨A - ε, B - ε, by linarith, by linarith, by linarith, by linarith, ?_⟩
  have hring : (1 - t) * (A - ε) + t * (B - ε)
      = ((1 - t) * A + t * B) - ε := by ring
  rw [hring]
  linarith

open scoped Pointwise in
private theorem measurable_brunn_minkowski_scaled {A B : Set ℝ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ENNReal.ofReal (1 - t) * volume A + ENNReal.ofReal t * volume B ≤
      volume ((fun x => (1 - t) * x) '' A + (fun y => t * y) '' B) := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have h1t' : (0 : ℝ) ≤ 1 - t := le_of_lt h1t
  have ht0' : (0 : ℝ) ≤ t := le_of_lt ht0
  have h1t_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 - t) := by
    rw [ENNReal.ofReal_pos]
    exact h1t
  have ht_pos : (0 : ℝ≥0∞) < ENNReal.ofReal t := by
    rw [ENNReal.ofReal_pos]
    exact ht0
  have h1t_ne : ENNReal.ofReal (1 - t) ≠ 0 := ne_of_gt h1t_pos
  have ht_ne : ENNReal.ofReal t ≠ 0 := ne_of_gt ht_pos
  by_cases hAinf : volume A = ⊤
  · obtain ⟨b0, hb0⟩ := hBne
    have hsub : (fun x => (1 - t) * x + t * b0) '' A ⊆
        (fun x => (1 - t) * x) '' A + (fun y => t * y) '' B := by
      rintro z ⟨y, hyA, rfl⟩
      exact Set.add_mem_add ⟨y, hyA, rfl⟩ ⟨b0, hb0, rfl⟩
    have hvol : volume ((fun x => (1 - t) * x + t * b0) '' A) = ⊤ := by
      rw [volume_image_affine_add_right A h1t', hAinf]
      rw [mul_comm]
      exact ENNReal.top_mul h1t_ne
    have hle : (⊤ : ℝ≥0∞) ≤
        volume ((fun x => (1 - t) * x) '' A + (fun y => t * y) '' B) := by
      rw [← hvol]
      exact measure_mono hsub
    have hLHS : ENNReal.ofReal (1 - t) * volume A + ENNReal.ofReal t * volume B
        = ⊤ := by
      rw [hAinf, mul_comm (ENNReal.ofReal (1 - t)) ⊤, ENNReal.top_mul h1t_ne]
      simp
    rw [hLHS]
    exact hle
  · by_cases hBinf : volume B = ⊤
    · obtain ⟨a0, ha0⟩ := hAne
      have hsub : (fun y => (1 - t) * a0 + t * y) '' B ⊆
          (fun x => (1 - t) * x) '' A + (fun y => t * y) '' B := by
        rintro z ⟨y, hyB, rfl⟩
        exact Set.add_mem_add ⟨a0, ha0, rfl⟩ ⟨y, hyB, rfl⟩
      have hvol : volume ((fun y => (1 - t) * a0 + t * y) '' B) = ⊤ := by
        rw [volume_image_affine_add_left B _ ht0', hBinf]
        rw [mul_comm]
        exact ENNReal.top_mul ht_ne
      have hle : (⊤ : ℝ≥0∞) ≤
          volume ((fun x => (1 - t) * x) '' A + (fun y => t * y) '' B) := by
        rw [← hvol]
        exact measure_mono hsub
      have hLHS : ENNReal.ofReal (1 - t) * volume A + ENNReal.ofReal t * volume B
          = ⊤ := by
        rw [hBinf, mul_comm (ENNReal.ofReal t) ⊤, ENNReal.top_mul ht_ne]
        simp
      rw [hLHS]
      exact hle
    · have hAfin : volume A ≠ ⊤ := hAinf
      have hBfin : volume B ≠ ⊤ := hBinf
      by_cases hA0 : volume A = 0
      · by_cases hB0 : volume B = 0
        · have hLHS : ENNReal.ofReal (1 - t) * volume A
              + ENNReal.ofReal t * volume B = 0 := by
            rw [hA0, hB0, mul_zero, mul_zero, add_zero]
          rw [hLHS]
          exact zero_le
        · obtain ⟨a0, ha0⟩ := hAne
          have hsub : (fun y => (1 - t) * a0 + t * y) '' B ⊆
              (fun x => (1 - t) * x) '' A + (fun y => t * y) '' B := by
            rintro z ⟨y, hyB, rfl⟩
            exact Set.add_mem_add ⟨a0, ha0, rfl⟩ ⟨y, hyB, rfl⟩
          have hvol : volume ((fun y => (1 - t) * a0 + t * y) '' B)
              = ENNReal.ofReal t * volume B :=
            volume_image_affine_add_left B _ ht0'
          have hle : ENNReal.ofReal t * volume B ≤
              volume ((fun x => (1 - t) * x) '' A + (fun y => t * y) '' B) := by
            rw [← hvol]
            exact measure_mono hsub
          have hLHS : ENNReal.ofReal (1 - t) * volume A
                + ENNReal.ofReal t * volume B = ENNReal.ofReal t * volume B := by
            rw [hA0, mul_zero, zero_add]
          rw [hLHS]
          exact hle
      · by_cases hB0 : volume B = 0
        · obtain ⟨b0, hb0⟩ := hBne
          have hsub : (fun x => (1 - t) * x + t * b0) '' A ⊆
              (fun x => (1 - t) * x) '' A + (fun y => t * y) '' B := by
            rintro z ⟨y, hyA, rfl⟩
            exact Set.add_mem_add ⟨y, hyA, rfl⟩ ⟨b0, hb0, rfl⟩
          have hvol : volume ((fun x => (1 - t) * x + t * b0) '' A)
              = ENNReal.ofReal (1 - t) * volume A :=
            volume_image_affine_add_right A h1t'
          have hle : ENNReal.ofReal (1 - t) * volume A ≤
              volume ((fun x => (1 - t) * x) '' A + (fun y => t * y) '' B) := by
            rw [← hvol]
            exact measure_mono hsub
          have hLHS : ENNReal.ofReal (1 - t) * volume A
                + ENNReal.ofReal t * volume B
              = ENNReal.ofReal (1 - t) * volume A := by
            rw [hB0, mul_zero, add_zero]
          rw [hLHS]
          exact hle
        · have hAne0 : volume A ≠ 0 := hA0
          have hBne0 : volume B ≠ 0 := hB0
          have hLHSfin : ENNReal.ofReal (1 - t) * volume A
              + ENNReal.ofReal t * volume B ≠ ⊤ := by
            rw [ENNReal.add_ne_top]
            constructor
            · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin
            · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin
          apply le_of_not_gt
          intro hlt
          have hRHSlt : volume ((fun x => (1 - t) * x) '' A
              + (fun y => t * y) '' B) < ⊤ :=
            lt_of_lt_of_le hlt le_top
          have hRHSfin : volume ((fun x => (1 - t) * x) '' A
              + (fun y => t * y) '' B) ≠ ⊤ :=
            lt_top_iff_ne_top.mp hRHSlt
          have hAtoPos : 0 < (volume A).toReal :=
            ENNReal.toReal_pos hAne0 hAfin
          have hBtoPos : 0 < (volume B).toReal :=
            ENNReal.toReal_pos hBne0 hBfin
          have hAeq : volume A = ENNReal.ofReal (volume A).toReal :=
            (ENNReal.ofReal_toReal hAfin).symm
          have hBeq : volume B = ENNReal.ofReal (volume B).toReal :=
            (ENNReal.ofReal_toReal hBfin).symm
          have hLHS_eq : ENNReal.ofReal (1 - t) * volume A
                + ENNReal.ofReal t * volume B
              = ENNReal.ofReal ((1 - t) * (volume A).toReal
                + t * (volume B).toReal) := by
            conv_lhs => rw [hAeq, hBeq, ← ENNReal.ofReal_mul h1t',
              ← ENNReal.ofReal_mul ht0']
            rw [← ENNReal.ofReal_add (mul_nonneg h1t' ENNReal.toReal_nonneg)
              (mul_nonneg ht0' ENNReal.toReal_nonneg)]
          have hceq : volume ((fun x => (1 - t) * x) '' A
                + (fun y => t * y) '' B)
              = ENNReal.ofReal (volume ((fun x => (1 - t) * x) '' A
                + (fun y => t * y) '' B)).toReal :=
            (ENNReal.ofReal_toReal hRHSfin).symm
          rw [hLHS_eq, hceq] at hlt
          have hDpos : 0 < (1 - t) * (volume A).toReal
              + t * (volume B).toReal := by
            apply add_pos
            · exact mul_pos h1t hAtoPos
            · exact mul_pos ht0 hBtoPos
          have hCreal : (volume ((fun x => (1 - t) * x) '' A
                + (fun y => t * y) '' B)).toReal
              < (1 - t) * (volume A).toReal + t * (volume B).toReal := by
            have h := (ENNReal.ofReal_lt_ofReal_iff hDpos).mp hlt
            exact h
          obtain ⟨r1, r2, hr1nn, hr1lt, hr2nn, hr2lt, hClt⟩ :=
            exists_lt_add_lt hAtoPos hBtoPos hCreal
          have hR1lt : ENNReal.ofReal r1 < volume A := by
            have h1 : ENNReal.ofReal r1
                < ENNReal.ofReal (volume A).toReal := by
              rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr1nn]
              exact hr1lt
            rw [ENNReal.ofReal_toReal hAfin] at h1
            exact h1
          have hR2lt : ENNReal.ofReal r2 < volume B := by
            have h1 : ENNReal.ofReal r2
                < ENNReal.ofReal (volume B).toReal := by
              rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr2nn]
              exact hr2lt
            rw [ENNReal.ofReal_toReal hBfin] at h1
            exact h1
          obtain ⟨K, hKA, hKcomp, hKR1⟩ :=
            hA.exists_lt_isCompact_of_ne_top hAfin hR1lt
          obtain ⟨L, hLB, hLcomp, hLR2⟩ :=
            hB.exists_lt_isCompact_of_ne_top hBfin hR2lt
          have hKpos : (0 : ℝ≥0∞) < volume K := by
            apply lt_of_le_of_lt _ hKR1
            exact zero_le
          have hLpos : (0 : ℝ≥0∞) < volume L := by
            apply lt_of_le_of_lt _ hLR2
            exact zero_le
          have hKne : K.Nonempty := by
            by_contra hcon
            rw [Set.not_nonempty_iff_eq_empty] at hcon
            rw [hcon] at hKpos
            simp at hKpos
          have hLne : L.Nonempty := by
            by_contra hcon
            rw [Set.not_nonempty_iff_eq_empty] at hcon
            rw [hcon] at hLpos
            simp at hLpos
          have hcomp := compact_brunn_minkowski_scaled ht0 ht1
            hKcomp hLcomp hKne hLne
          have hmono : (fun x => (1 - t) * x) '' K + (fun y => t * y) '' L ⊆
              (fun x => (1 - t) * x) '' A + (fun y => t * y) '' B := by
            apply Set.add_subset_add
            · exact Set.image_mono hKA
            · exact Set.image_mono hLB
          have hle2 : volume ((fun x => (1 - t) * x) '' K
                + (fun y => t * y) '' L)
              ≤ volume ((fun x => (1 - t) * x) '' A
                + (fun y => t * y) '' B) :=
            measure_mono hmono
          have hR12lt : ENNReal.ofReal ((1 - t) * r1 + t * r2)
              < ENNReal.ofReal (1 - t) * volume K
                + ENNReal.ofReal t * volume L := by
            have e1 : ENNReal.ofReal ((1 - t) * r1 + t * r2)
                = ENNReal.ofReal (1 - t) * ENNReal.ofReal r1
                  + ENNReal.ofReal t * ENNReal.ofReal r2 := by
              rw [ENNReal.ofReal_add (mul_nonneg h1t' hr1nn)
                (mul_nonneg ht0' hr2nn)]
              rw [ENNReal.ofReal_mul h1t', ENNReal.ofReal_mul ht0']
            rw [e1]
            apply ENNReal.add_lt_add
            · exact ENNReal.mul_lt_mul_right h1t_ne ENNReal.ofReal_ne_top hKR1
            · exact ENNReal.mul_lt_mul_right ht_ne ENNReal.ofReal_ne_top hLR2
          have hclt2 : volume ((fun x => (1 - t) * x) '' A
                + (fun y => t * y) '' B)
              < ENNReal.ofReal (1 - t) * volume K
                + ENNReal.ofReal t * volume L := by
            have h1 : volume ((fun x => (1 - t) * x) '' A
                  + (fun y => t * y) '' B)
                < ENNReal.ofReal ((1 - t) * r1 + t * r2) := by
              rw [hceq]
              have hnn : (0 : ℝ) ≤ (1 - t) * r1 + t * r2 := by
                apply add_nonneg
                · exact mul_nonneg h1t' hr1nn
                · exact mul_nonneg ht0' hr2nn
              have hpos2 : (0 : ℝ) < (1 - t) * r1 + t * r2 := by
                apply lt_of_le_of_lt _ hClt
                exact ENNReal.toReal_nonneg
              rw [ENNReal.ofReal_lt_ofReal_iff hpos2]
              exact hClt
            exact lt_trans h1 hR12lt
          have hcontra : volume ((fun x => (1 - t) * x) '' A
                + (fun y => t * y) '' B)
              < volume ((fun x => (1 - t) * x) '' A
                + (fun y => t * y) '' B) :=
            lt_of_lt_of_le hclt2 (le_trans hcomp hle2)
          exact (lt_irrefl _ hcontra).elim

private theorem lintegral_eq_lintegral_meas_lt_enNReal {α : Type*}
    [MeasurableSpace α] (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∫⁻ t in Set.Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} := by
  by_cases hinf : μ {x | f x = ⊤} = 0
  · have hf_toReal : Measurable fun x => (f x).toReal :=
      ENNReal.measurable_toReal.comp hf
    have hf_nn : 0 ≤ᵐ[μ] fun x => (f x).toReal :=
      Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg
    have hkey := MeasureTheory.lintegral_eq_lintegral_meas_lt μ hf_nn
      hf_toReal.aemeasurable
    have hmeas_top : MeasurableSet {x | f x = ⊤} :=
      hf (measurableSet_singleton ⊤)
    have hcongr : ∫⁻ x, f x ∂μ = ∫⁻ x, ENNReal.ofReal (f x).toReal ∂μ := by
      apply lintegral_congr_ae
      have hae : ∀ᵐ x ∂μ, f x ≠ ⊤ :=
        measure_eq_zero_iff_ae_notMem.mp hinf
      filter_upwards [hae] with x hx
      exact (ENNReal.ofReal_toReal hx).symm
    rw [hcongr, hkey]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have htpos : (0 : ℝ) < t := ht
    have hset : {x | ENNReal.ofReal t < f x}
        = {x | t < (f x).toReal} ∪ {x | f x = ⊤} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      by_cases hx : f x = ⊤
      · simp [hx, ENNReal.ofReal_lt_top]
      · have hfin : f x ≠ ⊤ := hx
        have heq : f x = ENNReal.ofReal (f x).toReal :=
          (ENNReal.ofReal_toReal hfin).symm
        rw [heq]
        rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt htpos)]
        simp [hx]
    change μ {x | t < (f x).toReal} = μ {x | ENNReal.ofReal t < f x}
    rw [hset]
    apply le_antisymm
    · exact measure_mono Set.subset_union_left
    · calc μ ({x | t < (f x).toReal} ∪ {x | f x = ⊤})
            ≤ μ {x | t < (f x).toReal} + μ {x | f x = ⊤} :=
              measure_union_le _ _
        _ = μ {x | t < (f x).toReal} := by rw [hinf, add_zero]
  · have hpos : (0 : ℝ≥0∞) < μ {x | f x = ⊤} := by
      apply lt_of_le_of_ne'
      · exact zero_le
      · exact hinf
    have hpos' : μ {x | f x = ⊤} ≠ 0 := ne_of_gt hpos
    have hLHS : ∫⁻ x, f x ∂μ = ⊤ := by
      apply eq_top_iff.mpr
      calc (⊤ : ℝ≥0∞) = ∫⁻ _ in {x | f x = ⊤}, ⊤ ∂μ := by
            simp [lintegral_const, hpos']
        _ = ∫⁻ x in {x | f x = ⊤}, f x ∂μ := by
            apply setLIntegral_congr_fun
            · exact hf (measurableSet_singleton ⊤)
            · intro x hx
              exact hx.symm
        _ ≤ ∫⁻ x, f x ∂μ := setLIntegral_le_lintegral _ _
    have hRHS : ∫⁻ t in Set.Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} = ⊤ := by
      apply eq_top_iff.mpr
      have hle : ∀ t : ℝ, t ∈ Set.Ioi (0 : ℝ) →
          μ {x | f x = ⊤} ≤ μ {x | ENNReal.ofReal t < f x} := by
        intro t ht
        apply measure_mono
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [hx]
        exact ENNReal.ofReal_lt_top
      have hmono : ∫⁻ _ in Set.Ioi (0 : ℝ), μ {x | f x = ⊤} ∂volume
          ≤ ∫⁻ t in Set.Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        exact hle t ht
      have hconst : ∫⁻ _ in Set.Ioi (0 : ℝ), μ {x | f x = ⊤} ∂volume = ⊤ := by
        rw [lintegral_const]
        simp [Real.volume_Ioi, hpos']
      rw [← hconst]
      exact hmono
    rw [hLHS, hRHS]

private theorem measurable_tail_measure {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun t : ℝ => volume {x : ℝ | ENNReal.ofReal t < f x} := by
  have h1 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst
  have h2 : Measurable fun p : ℝ × ℝ => f p.2 :=
    hf.comp measurable_snd
  have hs : MeasurableSet {p : ℝ × ℝ | ENNReal.ofReal p.1 < f p.2} :=
    measurableSet_lt h1 h2
  have hmeas : Measurable fun t : ℝ => volume {x : ℝ | (t, x) ∈
      {p : ℝ × ℝ | ENNReal.ofReal p.1 < f p.2}} :=
    measurable_measure_prodMk_left hs
  exact hmeas

private theorem setLIntegral_Ioi_scaling {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    {a : ℝ} (ha : 0 < a) :
    ∫⁻ u in Set.Ioi (0 : ℝ), F (a * u)
      = (ENNReal.ofReal a)⁻¹ * ∫⁻ r in Set.Ioi (0 : ℝ), F r := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hmeas_mul : Measurable fun u : ℝ => a * u :=
    measurable_const_mul a
  have hpre : (fun u : ℝ => a * u) ⁻¹' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor
    · intro h
      exact pos_of_mul_pos_right h (le_of_lt ha)
    · intro h
      exact mul_pos ha h
  have hmap := Real.map_volume_mul_left hane
  have h1 : ∫⁻ u in Set.Ioi (0 : ℝ), F (a * u) ∂volume
      = ∫⁻ r in Set.Ioi (0 : ℝ), F r ∂Measure.map (fun u => a * u) volume := by
    rw [setLIntegral_map measurableSet_Ioi hF hmeas_mul, hpre]
  rw [h1, hmap, setLIntegral_smul_measure]
  have hab : |a⁻¹| = a⁻¹ := abs_of_pos (inv_pos.mpr ha)
  rw [hab, ENNReal.ofReal_inv_of_pos ha, smul_eq_mul]

open scoped Pointwise in
private theorem superlevel_inclusion_1d {f g h : ℝ → ℝ≥0∞} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hfgh : ∀ x y : ℝ, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y))
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (fun x => (1 - t) * x) '' {x | ENNReal.ofReal r < f x}
      + (fun y => t * y) '' {y | ENNReal.ofReal s < g y}
      ⊆ {z | ENNReal.ofReal (r ^ (1 - t) * s ^ t) < h z} := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hrpow_pos : (0 : ℝ) < r ^ (1 - t) := Real.rpow_pos_of_pos hr _
  have hspow_pos : (0 : ℝ) < s ^ t := Real.rpow_pos_of_pos hs _
  have h1 : ENNReal.ofReal (r ^ (1 - t))
      = (ENNReal.ofReal r) ^ (1 - t) :=
    (ENNReal.ofReal_rpow_of_pos hr).symm
  have h2 : ENNReal.ofReal (s ^ t) = (ENNReal.ofReal s) ^ t :=
    (ENNReal.ofReal_rpow_of_pos hs).symm
  have h3 : ENNReal.ofReal (r ^ (1 - t) * s ^ t)
      = ENNReal.ofReal (r ^ (1 - t)) * ENNReal.ofReal (s ^ t) := by
    rw [ENNReal.ofReal_mul (le_of_lt hrpow_pos)]
  rintro z hz
  rw [Set.mem_add] at hz
  obtain ⟨a, ⟨x, hx, rfl⟩, b, ⟨y, hy, rfl⟩, rfl⟩ := hz
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hfx : ENNReal.ofReal r ^ (1 - t) < f x ^ (1 - t) :=
    (ENNReal.strictMono_rpow_of_pos h1t) hx
  have hgy : ENNReal.ofReal s ^ t < g y ^ t :=
    (ENNReal.strictMono_rpow_of_pos ht0) hy
  have hmul : ENNReal.ofReal r ^ (1 - t) * ENNReal.ofReal s ^ t
      < f x ^ (1 - t) * g y ^ t := by
    apply ENNReal.mul_lt_mul hfx hgy
  rw [← h1, ← h2, ← h3] at hmul
  have hsmul : (1 - t) • x + t • y = (1 - t) * x + t * y := by
    simp [smul_eq_mul]
  rw [← hsmul]
  exact lt_of_lt_of_le hmul (hfgh x y)

private theorem nonempty_superlevel_of_lt_sSup {f : ℝ → ℝ≥0∞} {r : ℝ}
    (h : ENNReal.ofReal r < sSup (Set.range f)) :
    {x | ENNReal.ofReal r < f x}.Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hle : ∀ x : ℝ, f x ≤ ENNReal.ofReal r := by
    intro x
    by_contra hcon2
    have hlt : ENNReal.ofReal r < f x := lt_of_not_ge hcon2
    have hmem : x ∈ {x | ENNReal.ofReal r < f x} := hlt
    rw [hcon] at hmem
    simp at hmem
  have hsSup : sSup (Set.range f) ≤ ENNReal.ofReal r := by
    apply sSup_le
    intro a ha
    obtain ⟨x, rfl⟩ := ha
    exact hle x
  exact not_lt_of_ge hsSup h

private theorem prekopa_leindler_1d_real {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfgh : ∀ x y : ℝ, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x ∂volume) ^ (1 - t) * (∫⁻ x, g x ∂volume) ^ t
      ≤ ∫⁻ x, h x ∂volume := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  by_cases hf0 : (∫⁻ x, f x ∂volume) = 0
  · have hF : (∫⁻ x, f x ∂volume) ^ (1 - t) = 0 := by
      rw [hf0]
      exact ENNReal.zero_rpow_of_pos h1t
    rw [hF, zero_mul]
    exact zero_le
  · by_cases hg0 : (∫⁻ x, g x ∂volume) = 0
    · have hG : (∫⁻ x, g x ∂volume) ^ t = 0 := by
        rw [hg0]
        exact ENNReal.zero_rpow_of_pos ht0
      rw [hG, mul_zero]
      exact zero_le
    · have hAne0 : (∫⁻ x, f x ∂volume) ≠ 0 := hf0
      have hBne0 : (∫⁻ x, g x ∂volume) ≠ 0 := hg0
      set Mf : ℝ≥0∞ := sSup (Set.range f) with hMfdef
      set Mg : ℝ≥0∞ := sSup (Set.range g) with hMgdef
      have hMf_nn : (0 : ℝ≥0∞) ≤ Mf := by
        have h0 : f 0 ≤ Mf := le_sSup (Set.mem_range_self 0)
        exact le_trans zero_le h0
      have hMg_nn : (0 : ℝ≥0∞) ≤ Mg := by
        have h0 : g 0 ≤ Mg := le_sSup (Set.mem_range_self 0)
        exact le_trans zero_le h0
      have hMf_ne : Mf ≠ 0 := by
        intro hcon
        have hzero : ∀ x : ℝ, f x = 0 := by
          intro x
          have hle : f x ≤ Mf := le_sSup (Set.mem_range_self x)
          rw [hcon] at hle
          exact le_antisymm hle zero_le
        have hint : (∫⁻ x, f x ∂volume) = 0 := by
          have : f = fun _ => 0 := funext hzero
          rw [this]
          exact lintegral_zero
        exact hAne0 hint
      have hMg_ne : Mg ≠ 0 := by
        intro hcon
        have hzero : ∀ x : ℝ, g x = 0 := by
          intro x
          have hle : g x ≤ Mg := le_sSup (Set.mem_range_self x)
          rw [hcon] at hle
          exact le_antisymm hle zero_le
        have hint : (∫⁻ x, g x ∂volume) = 0 := by
          have : g = fun _ => 0 := funext hzero
          rw [this]
          exact lintegral_zero
        exact hBne0 hint
      have hMf_pos : (0 : ℝ≥0∞) < Mf := lt_of_le_of_ne' hMf_nn hMf_ne
      have hMg_pos : (0 : ℝ≥0∞) < Mg := lt_of_le_of_ne' hMg_nn hMg_ne
      by_cases hMfTop : Mf = ⊤
      · by_cases hMgTop : Mg = ⊤
        · have hpow : ∀ u : ℝ, 0 < u → u ^ (1 - t) * u ^ t = u := by
            intro u hu
            have h1 : u ^ (1 - t) * u ^ t = u ^ ((1 - t) + t) := by
              rw [← Real.rpow_add hu]
            have h2 : (1 - t) + t = 1 := by ring
            rw [h1, h2, Real.rpow_one]
          have hpoint : ∀ u : ℝ, u ∈ Set.Ioi (0 : ℝ) →
              ENNReal.ofReal (1 - t)
                  * volume {x | ENNReal.ofReal u < f x}
                + ENNReal.ofReal t * volume {y | ENNReal.ofReal u < g y}
                ≤ volume {z | ENNReal.ofReal u < h z} := by
            intro u hu
            have hupos : (0 : ℝ) < u := hu
            have hrw : u ^ (1 - t) * u ^ t = u := hpow u hupos
            have hsub := superlevel_inclusion_1d ht0 ht1 hfgh hupos hupos
            rw [hrw] at hsub
            have hne1 : {x | ENNReal.ofReal u < f x}.Nonempty := by
              apply nonempty_superlevel_of_lt_sSup
              rw [← hMfdef, hMfTop]
              exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
            have hne2 : {y | ENNReal.ofReal u < g y}.Nonempty := by
              apply nonempty_superlevel_of_lt_sSup
              rw [← hMgdef, hMgTop]
              exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
            have hmeas1 : MeasurableSet {x | ENNReal.ofReal u < f x} :=
              measurableSet_lt measurable_const hf
            have hmeas2 : MeasurableSet {y | ENNReal.ofReal u < g y} :=
              measurableSet_lt measurable_const hg
            have hbm := measurable_brunn_minkowski_scaled ht0 ht1
              hmeas1 hmeas2 hne1 hne2
            exact le_trans hbm (measure_mono hsub)
          have hFmeas : Measurable fun t : ℝ =>
              volume {x : ℝ | ENNReal.ofReal t < f x} :=
            measurable_tail_measure hf
          have hGmeas : Measurable fun t : ℝ =>
              volume {y : ℝ | ENNReal.ofReal t < g y} :=
            measurable_tail_measure hg
          have hHmeas : Measurable fun t : ℝ =>
              volume {z : ℝ | ENNReal.ofReal t < h z} :=
            measurable_tail_measure hh
          have hlayF := lintegral_eq_lintegral_meas_lt_enNReal volume hf
          have hlayG := lintegral_eq_lintegral_meas_lt_enNReal volume hg
          have hlayH := lintegral_eq_lintegral_meas_lt_enNReal volume hh
          have hinter : ENNReal.ofReal (1 - t) * (∫⁻ x, f x ∂volume)
                + ENNReal.ofReal t * (∫⁻ x, g x ∂volume)
              ≤ ∫⁻ x, h x ∂volume := by
            rw [hlayF, hlayG, hlayH]
            have h1 : ENNReal.ofReal (1 - t)
                  * ∫⁻ u in Set.Ioi (0 : ℝ),
                    volume {x | ENNReal.ofReal u < f x}
                = ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (1 - t)
                    * volume {x | ENNReal.ofReal u < f x} :=
              (lintegral_const_mul _ hFmeas).symm
            have h2 : ENNReal.ofReal t
                  * ∫⁻ u in Set.Ioi (0 : ℝ),
                    volume {y | ENNReal.ofReal u < g y}
                = ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal t
                    * volume {y | ENNReal.ofReal u < g y} :=
              (lintegral_const_mul _ hGmeas).symm
            have hF'' : Measurable fun u : ℝ => ENNReal.ofReal (1 - t)
                * volume {x : ℝ | ENNReal.ofReal u < f x} :=
              hFmeas.const_mul _
            rw [h1, h2, ← lintegral_add_left hF'' _]
            apply setLIntegral_mono' measurableSet_Ioi
            intro u hu
            exact hpoint u hu
          exact le_trans (ennreal_geom_mean_le_arith_mean2 _ _ ht0 ht1) hinter
        · have hlayG := lintegral_eq_lintegral_meas_lt_enNReal volume hg
          have hlayH := lintegral_eq_lintegral_meas_lt_enNReal volume hh
          have hex : ∃ d : ℝ, 0 < d ∧ (0 : ℝ≥0∞)
              < volume {y | ENNReal.ofReal d < g y} := by
            by_contra hcon
            have hzero : ∀ d : ℝ, d ∈ Set.Ioi (0 : ℝ) →
                volume {y | ENNReal.ofReal d < g y} = 0 := by
              intro d hd
              have hdpos : (0 : ℝ) < d := hd
              by_contra hne
              have hpos : (0 : ℝ≥0∞)
                  < volume {y | ENNReal.ofReal d < g y} := by
                apply lt_of_le_of_ne'
                · exact zero_le
                · exact hne
              exact hcon ⟨d, hdpos, hpos⟩
            have hint : (∫⁻ x, g x ∂volume) = 0 := by
              rw [hlayG]
              have hcongr : (∫⁻ t in Set.Ioi (0 : ℝ),
                    volume {y | ENNReal.ofReal t < g y})
                  = ∫⁻ t in Set.Ioi (0 : ℝ), 0 := by
                apply setLIntegral_congr_fun measurableSet_Ioi
                intro t ht
                exact hzero t ht
              rw [hcongr]
              simp
            exact hBne0 hint
          obtain ⟨d, hdpos, hGdpos⟩ := hex
          have hdtpos : (0 : ℝ) < d ^ t := Real.rpow_pos_of_pos hdpos _
          have hdtne : d ^ t ≠ 0 := ne_of_gt hdtpos
          have ht_pos : (0 : ℝ≥0∞) < ENNReal.ofReal t := by
            rw [ENNReal.ofReal_pos]
            exact ht0
          have hcpos : (0 : ℝ≥0∞)
              < ENNReal.ofReal t * volume {y | ENNReal.ofReal d < g y} :=
            ENNReal.mul_pos (ne_of_gt ht_pos) (ne_of_gt hGdpos)
          have hpoint : ∀ u : ℝ, u ∈ Set.Ioi (0 : ℝ) →
              ENNReal.ofReal t * volume {y | ENNReal.ofReal d < g y}
                ≤ volume {z | ENNReal.ofReal u < h z} := by
            intro u hu
            have hupos : (0 : ℝ) < u := hu
            have h1tne : (1 : ℝ) - t ≠ 0 := ne_of_gt h1t
            set r : ℝ := (u / d ^ t) ^ ((1 - t)⁻¹) with hrdef
            have hudt : (0 : ℝ) < u / d ^ t := div_pos hupos hdtpos
            have hrpos : (0 : ℝ) < r := Real.rpow_pos_of_pos hudt _
            have hrrw : r ^ (1 - t) * d ^ t = u := by
              have e1 : r ^ (1 - t) = u / d ^ t := by
                have h := (Real.eq_rpow_inv (le_of_lt hrpos)
                  (le_of_lt hudt) h1tne).mp hrdef
                exact h
              rw [e1]
              rw [div_mul_cancel₀ u hdtne]
            have hsub := superlevel_inclusion_1d ht0 ht1 hfgh hrpos hdpos
            rw [hrrw] at hsub
            have hne1 : {x | ENNReal.ofReal r < f x}.Nonempty := by
              apply nonempty_superlevel_of_lt_sSup
              rw [← hMfdef, hMfTop]
              exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
            have hne2 : {y | ENNReal.ofReal d < g y}.Nonempty := by
              by_contra hcon
              rw [Set.not_nonempty_iff_eq_empty] at hcon
              rw [hcon] at hGdpos
              simp at hGdpos
            have hmeas1 : MeasurableSet {x | ENNReal.ofReal r < f x} :=
              measurableSet_lt measurable_const hf
            have hmeas2 : MeasurableSet {y | ENNReal.ofReal d < g y} :=
              measurableSet_lt measurable_const hg
            have hbm := measurable_brunn_minkowski_scaled ht0 ht1
              hmeas1 hmeas2 hne1 hne2
            have hle := le_trans hbm (measure_mono hsub)
            exact le_trans (le_add_of_nonneg_left zero_le) hle
          have hHtop : ∫⁻ x, h x ∂volume = ⊤ := by
            rw [hlayH]
            apply eq_top_iff.mpr
            have hmono : ∫⁻ _ in Set.Ioi (0 : ℝ),
                  ENNReal.ofReal t * volume {y | ENNReal.ofReal d < g y}
                  ∂volume
                ≤ ∫⁻ u in Set.Ioi (0 : ℝ),
                  volume {z | ENNReal.ofReal u < h z} := by
              apply setLIntegral_mono' measurableSet_Ioi
              intro u hu
              exact hpoint u hu
            have hconst : ∫⁻ _ in Set.Ioi (0 : ℝ),
                  ENNReal.ofReal t * volume {y | ENNReal.ofReal d < g y}
                  ∂volume = ⊤ := by
              rw [lintegral_const, Measure.restrict_apply_univ]
              have hvol : volume (Set.Ioi (0 : ℝ)) = ⊤ := Real.volume_Ioi
              rw [hvol]
              have hne : ENNReal.ofReal t
                  * volume {y | ENNReal.ofReal d < g y} ≠ 0 :=
                ne_of_gt hcpos
              rw [mul_comm]
              exact ENNReal.top_mul hne
            rw [← hconst]
            exact hmono
          rw [hHtop]
          exact le_top
      · by_cases hMgTop : Mg = ⊤
        · have hlayF := lintegral_eq_lintegral_meas_lt_enNReal volume hf
          have hlayH := lintegral_eq_lintegral_meas_lt_enNReal volume hh
          have hex : ∃ c : ℝ, 0 < c ∧ (0 : ℝ≥0∞)
              < volume {x | ENNReal.ofReal c < f x} := by
            by_contra hcon
            have hzero : ∀ c : ℝ, c ∈ Set.Ioi (0 : ℝ) →
                volume {x | ENNReal.ofReal c < f x} = 0 := by
              intro c hc
              have hcpos : (0 : ℝ) < c := hc
              by_contra hne
              have hpos : (0 : ℝ≥0∞)
                  < volume {x | ENNReal.ofReal c < f x} := by
                apply lt_of_le_of_ne'
                · exact zero_le
                · exact hne
              exact hcon ⟨c, hcpos, hpos⟩
            have hint : (∫⁻ x, f x ∂volume) = 0 := by
              rw [hlayF]
              have hcongr : (∫⁻ t in Set.Ioi (0 : ℝ),
                    volume {x | ENNReal.ofReal t < f x})
                  = ∫⁻ t in Set.Ioi (0 : ℝ), 0 := by
                apply setLIntegral_congr_fun measurableSet_Ioi
                intro t ht
                exact hzero t ht
              rw [hcongr]
              simp
            exact hAne0 hint
          obtain ⟨c, hc0, hFcpos⟩ := hex
          have hctpos : (0 : ℝ) < c ^ (1 - t) := Real.rpow_pos_of_pos hc0 _
          have hctne : c ^ (1 - t) ≠ 0 := ne_of_gt hctpos
          have htne : t ≠ 0 := ne_of_gt ht0
          have h1t_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 - t) := by
            rw [ENNReal.ofReal_pos]
            exact h1t
          have hcpos : (0 : ℝ≥0∞)
              < ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal c < f x} :=
            ENNReal.mul_pos (ne_of_gt h1t_pos) (ne_of_gt hFcpos)
          have hpoint : ∀ u : ℝ, u ∈ Set.Ioi (0 : ℝ) →
              ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal c < f x}
                ≤ volume {z | ENNReal.ofReal u < h z} := by
            intro u hu
            have hupos : (0 : ℝ) < u := hu
            set s : ℝ := (u / c ^ (1 - t)) ^ (t⁻¹) with hsdef
            have huct : (0 : ℝ) < u / c ^ (1 - t) := div_pos hupos hctpos
            have hspos : (0 : ℝ) < s := Real.rpow_pos_of_pos huct _
            have hsrw : c ^ (1 - t) * s ^ t = u := by
              have e1 : s ^ t = u / c ^ (1 - t) := by
                have h := (Real.eq_rpow_inv (le_of_lt hspos)
                  (le_of_lt huct) htne).mp hsdef
                exact h
              rw [e1, mul_comm (c ^ (1 - t)), div_mul_cancel₀ u hctne]
            have hsub := superlevel_inclusion_1d ht0 ht1 hfgh hc0 hspos
            rw [hsrw] at hsub
            have hne1 : {x | ENNReal.ofReal c < f x}.Nonempty := by
              by_contra hcon
              rw [Set.not_nonempty_iff_eq_empty] at hcon
              rw [hcon] at hFcpos
              simp at hFcpos
            have hne2 : {y | ENNReal.ofReal s < g y}.Nonempty := by
              apply nonempty_superlevel_of_lt_sSup
              rw [← hMgdef, hMgTop]
              exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
            have hmeas1 : MeasurableSet {x | ENNReal.ofReal c < f x} :=
              measurableSet_lt measurable_const hf
            have hmeas2 : MeasurableSet {y | ENNReal.ofReal s < g y} :=
              measurableSet_lt measurable_const hg
            have hbm := measurable_brunn_minkowski_scaled ht0 ht1
              hmeas1 hmeas2 hne1 hne2
            have hle := le_trans hbm (measure_mono hsub)
            exact le_trans (le_add_of_nonneg_right zero_le) hle
          have hHtop : ∫⁻ x, h x ∂volume = ⊤ := by
            rw [hlayH]
            apply eq_top_iff.mpr
            have hmono : ∫⁻ _ in Set.Ioi (0 : ℝ),
                  ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal c < f x}
                  ∂volume
                ≤ ∫⁻ u in Set.Ioi (0 : ℝ),
                  volume {z | ENNReal.ofReal u < h z} := by
              apply setLIntegral_mono' measurableSet_Ioi
              intro u hu
              exact hpoint u hu
            have hconst : ∫⁻ _ in Set.Ioi (0 : ℝ),
                  ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal c < f x}
                  ∂volume = ⊤ := by
              rw [lintegral_const, Measure.restrict_apply_univ]
              have hvol : volume (Set.Ioi (0 : ℝ)) = ⊤ := Real.volume_Ioi
              rw [hvol]
              have hne : ENNReal.ofReal (1 - t)
                  * volume {x | ENNReal.ofReal c < f x} ≠ 0 :=
                ne_of_gt hcpos
              rw [mul_comm]
              exact ENNReal.top_mul hne
            rw [← hconst]
            exact hmono
          rw [hHtop]
          exact le_top
        · have h1t' : (0 : ℝ) ≤ 1 - t := le_of_lt h1t
          have ht0' : (0 : ℝ) ≤ t := le_of_lt ht0
          have hApos : (0 : ℝ) < Mf.toReal := ENNReal.toReal_pos hMf_ne hMfTop
          have hBpos : (0 : ℝ) < Mg.toReal := ENNReal.toReal_pos hMg_ne hMgTop
          have hMf_eq : Mf = ENNReal.ofReal Mf.toReal :=
            (ENNReal.ofReal_toReal hMfTop).symm
          have hMg_eq : Mg = ENNReal.ofReal Mg.toReal :=
            (ENNReal.ofReal_toReal hMgTop).symm
          set A : ℝ := Mf.toReal
          set B : ℝ := Mg.toReal
          set C : ℝ := A ^ (1 - t) * B ^ t with hCdef
          have hCpos : (0 : ℝ) < C :=
            mul_pos (Real.rpow_pos_of_pos hApos _) (Real.rpow_pos_of_pos hBpos _)
          have hkey : ∀ u : ℝ, 0 < u → (A * u) ^ (1 - t) * (B * u) ^ t = C * u := by
            intro u hu
            have e1 : (A * u) ^ (1 - t) = A ^ (1 - t) * u ^ (1 - t) :=
              Real.mul_rpow (le_of_lt hApos) (le_of_lt hu)
            have e2 : (B * u) ^ t = B ^ t * u ^ t :=
              Real.mul_rpow (le_of_lt hBpos) (le_of_lt hu)
            have e3 : u ^ (1 - t) * u ^ t = u := by
              have h1 : u ^ (1 - t) * u ^ t = u ^ ((1 - t) + t) := by
                rw [← Real.rpow_add hu]
              have h2 : (1 - t) + t = 1 := by ring
              rw [h1, h2, Real.rpow_one]
            rw [e1, e2, hCdef]
            have hring : A ^ (1 - t) * u ^ (1 - t) * (B ^ t * u ^ t)
                = (A ^ (1 - t) * B ^ t) * (u ^ (1 - t) * u ^ t) := by ring
            rw [hring, e3]
          have hpoint : ∀ u : ℝ, u ∈ Set.Ioi (0 : ℝ) →
              ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal (A * u) < f x}
                + ENNReal.ofReal t * volume {y | ENNReal.ofReal (B * u) < g y}
                ≤ volume {z | ENNReal.ofReal (C * u) < h z} := by
            intro u hu
            have hupos : (0 : ℝ) < u := hu
            have hr : (0 : ℝ) < A * u := mul_pos hApos hupos
            have hs : (0 : ℝ) < B * u := mul_pos hBpos hupos
            by_cases hu1 : u < 1
            · have hrA : A * u < A := by
                have hlt := mul_lt_mul_of_pos_left hu1 hApos
                rwa [mul_one] at hlt
              have hsB : B * u < B := by
                have hlt := mul_lt_mul_of_pos_left hu1 hBpos
                rwa [mul_one] at hlt
              have hne1 : {x | ENNReal.ofReal (A * u) < f x}.Nonempty := by
                apply nonempty_superlevel_of_lt_sSup
                rw [← hMfdef, hMf_eq]
                rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hr)]
                exact hrA
              have hne2 : {y | ENNReal.ofReal (B * u) < g y}.Nonempty := by
                apply nonempty_superlevel_of_lt_sSup
                rw [← hMgdef, hMg_eq]
                rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hs)]
                exact hsB
              have hmeas1 : MeasurableSet {x | ENNReal.ofReal (A * u) < f x} :=
                measurableSet_lt measurable_const hf
              have hmeas2 : MeasurableSet {y | ENNReal.ofReal (B * u) < g y} :=
                measurableSet_lt measurable_const hg
              have hbm := measurable_brunn_minkowski_scaled ht0 ht1
                hmeas1 hmeas2 hne1 hne2
              have hsub := superlevel_inclusion_1d ht0 ht1 hfgh hr hs
              rw [hkey u hupos] at hsub
              exact le_trans hbm (measure_mono hsub)
            · push Not at hu1
              have hAu : A ≤ A * u := by
                conv_lhs => rw [← mul_one A]
                exact mul_le_mul_of_nonneg_left hu1 (le_of_lt hApos)
              have hBu : B ≤ B * u := by
                conv_lhs => rw [← mul_one B]
                exact mul_le_mul_of_nonneg_left hu1 (le_of_lt hBpos)
              have hempty1 : {x | ENNReal.ofReal (A * u) < f x} = ∅ := by
                rw [Set.eq_empty_iff_forall_notMem]
                intro x hx
                simp only [Set.mem_ofPred_eq] at hx
                have hfx : f x ≤ Mf := le_sSup (Set.mem_range_self x)
                rw [hMf_eq] at hfx
                have hle : ENNReal.ofReal A ≤ ENNReal.ofReal (A * u) :=
                  ENNReal.ofReal_le_ofReal hAu
                exact absurd (lt_of_le_of_lt (le_trans hfx hle) hx) (lt_irrefl _)
              have hempty2 : {y | ENNReal.ofReal (B * u) < g y} = ∅ := by
                rw [Set.eq_empty_iff_forall_notMem]
                intro y hy
                simp only [Set.mem_ofPred_eq] at hy
                have hgy : g y ≤ Mg := le_sSup (Set.mem_range_self y)
                rw [hMg_eq] at hgy
                have hle : ENNReal.ofReal B ≤ ENNReal.ofReal (B * u) :=
                  ENNReal.ofReal_le_ofReal hBu
                exact absurd (lt_of_le_of_lt (le_trans hgy hle) hy) (lt_irrefl _)
              rw [hempty1, hempty2, measure_empty, mul_zero, mul_zero, add_zero]
              exact zero_le
          have hFmeas : Measurable fun t : ℝ =>
              volume {x : ℝ | ENNReal.ofReal t < f x} :=
            measurable_tail_measure hf
          have hGmeas : Measurable fun t : ℝ =>
              volume {y : ℝ | ENNReal.ofReal t < g y} :=
            measurable_tail_measure hg
          have hHmeas : Measurable fun t : ℝ =>
              volume {z : ℝ | ENNReal.ofReal t < h z} :=
            measurable_tail_measure hh
          have hlayF := lintegral_eq_lintegral_meas_lt_enNReal volume hf
          have hlayG := lintegral_eq_lintegral_meas_lt_enNReal volume hg
          have hlayH := lintegral_eq_lintegral_meas_lt_enNReal volume hh
          have hFscale : ∫⁻ u in Set.Ioi (0 : ℝ),
                volume {x | ENNReal.ofReal (A * u) < f x}
              = (ENNReal.ofReal A)⁻¹ * ∫⁻ x, f x ∂volume := by
            have hsc := setLIntegral_Ioi_scaling hFmeas hApos
            rw [hlayF]
            exact hsc
          have hGscale : ∫⁻ u in Set.Ioi (0 : ℝ),
                volume {y | ENNReal.ofReal (B * u) < g y}
              = (ENNReal.ofReal B)⁻¹ * ∫⁻ x, g x ∂volume := by
            have hsc := setLIntegral_Ioi_scaling hGmeas hBpos
            rw [hlayG]
            exact hsc
          have hHscale : ∫⁻ u in Set.Ioi (0 : ℝ),
                volume {z | ENNReal.ofReal (C * u) < h z}
              = (ENNReal.ofReal C)⁻¹ * ∫⁻ x, h x ∂volume := by
            have hsc := setLIntegral_Ioi_scaling hHmeas hCpos
            rw [hlayH]
            exact hsc
          have hFcomp : Measurable fun u : ℝ =>
              volume {x : ℝ | ENNReal.ofReal (A * u) < f x} :=
            hFmeas.comp (measurable_const_mul A)
          have hGcomp : Measurable fun u : ℝ =>
              volume {y : ℝ | ENNReal.ofReal (B * u) < g y} :=
            hGmeas.comp (measurable_const_mul B)
          have hinter : ENNReal.ofReal (1 - t)
                * ((ENNReal.ofReal A)⁻¹ * ∫⁻ x, f x ∂volume)
              + ENNReal.ofReal t * ((ENNReal.ofReal B)⁻¹ * ∫⁻ x, g x ∂volume)
              ≤ (ENNReal.ofReal C)⁻¹ * ∫⁻ x, h x ∂volume := by
            rw [← hFscale, ← hGscale, ← hHscale]
            have h1 : ENNReal.ofReal (1 - t)
                  * ∫⁻ u in Set.Ioi (0 : ℝ),
                    volume {x | ENNReal.ofReal (A * u) < f x}
                = ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (1 - t)
                    * volume {x | ENNReal.ofReal (A * u) < f x} :=
              (lintegral_const_mul _ hFcomp).symm
            have h2 : ENNReal.ofReal t
                  * ∫⁻ u in Set.Ioi (0 : ℝ),
                    volume {y | ENNReal.ofReal (B * u) < g y}
                = ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal t
                    * volume {y | ENNReal.ofReal (B * u) < g y} :=
              (lintegral_const_mul _ hGcomp).symm
            have hF'' : Measurable fun u : ℝ => ENNReal.ofReal (1 - t)
                * volume {x : ℝ | ENNReal.ofReal (A * u) < f x} :=
              hFcomp.const_mul _
            rw [h1, h2, ← lintegral_add_left hF'' _]
            apply setLIntegral_mono' measurableSet_Ioi
            intro u hu
            exact hpoint u hu
          have ha0 : ENNReal.ofReal A ≠ 0 := (ENNReal.ofReal_pos.mpr hApos).ne'
          have haT : ENNReal.ofReal A ≠ ⊤ := ENNReal.ofReal_ne_top
          have hb0 : ENNReal.ofReal B ≠ 0 := (ENNReal.ofReal_pos.mpr hBpos).ne'
          have hbT : ENNReal.ofReal B ≠ ⊤ := ENNReal.ofReal_ne_top
          have hc0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hCpos).ne'
          have hcT : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
          have hc_eq : ENNReal.ofReal C
              = (ENNReal.ofReal A) ^ (1 - t) * (ENNReal.ofReal B) ^ t := by
            rw [hCdef, ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hApos) _),
              ← ENNReal.ofReal_rpow_of_pos hApos,
              ← ENNReal.ofReal_rpow_of_pos hBpos]
          have eX : ((ENNReal.ofReal A)⁻¹ * ∫⁻ x, f x ∂volume) ^ (1 - t)
              = (ENNReal.ofReal A)⁻¹ ^ (1 - t)
                * (∫⁻ x, f x ∂volume) ^ (1 - t) :=
            ENNReal.mul_rpow_of_nonneg _ _ h1t'
          have eY : ((ENNReal.ofReal B)⁻¹ * ∫⁻ x, g x ∂volume) ^ t
              = (ENNReal.ofReal B)⁻¹ ^ t * (∫⁻ x, g x ∂volume) ^ t :=
            ENNReal.mul_rpow_of_nonneg _ _ ht0'
          have hAa : (ENNReal.ofReal A) ^ (1 - t)
              * (ENNReal.ofReal A)⁻¹ ^ (1 - t) = 1 := by
            rw [← ENNReal.mul_rpow_of_nonneg _ _ h1t',
              ENNReal.mul_inv_cancel ha0 haT, ENNReal.one_rpow]
          have hBb : (ENNReal.ofReal B) ^ t * (ENNReal.ofReal B)⁻¹ ^ t = 1 := by
            rw [← ENNReal.mul_rpow_of_nonneg _ _ ht0',
              ENNReal.mul_inv_cancel hb0 hbT, ENNReal.one_rpow]
          have hkey2 : (∫⁻ x, f x ∂volume) ^ (1 - t)
                * (∫⁻ x, g x ∂volume) ^ t
              = ENNReal.ofReal C
                * (((ENNReal.ofReal A)⁻¹ * ∫⁻ x, f x ∂volume) ^ (1 - t)
                  * ((ENNReal.ofReal B)⁻¹ * ∫⁻ x, g x ∂volume) ^ t) := by
            rw [hc_eq, eX, eY]
            have hring : ((ENNReal.ofReal A) ^ (1 - t)
                  * (ENNReal.ofReal B) ^ t)
                  * (((ENNReal.ofReal A)⁻¹ ^ (1 - t)
                    * (∫⁻ x, f x ∂volume) ^ (1 - t))
                    * ((ENNReal.ofReal B)⁻¹ ^ t * (∫⁻ x, g x ∂volume) ^ t))
                = ((ENNReal.ofReal A) ^ (1 - t)
                    * (ENNReal.ofReal A)⁻¹ ^ (1 - t))
                  * ((ENNReal.ofReal B) ^ t * (ENNReal.ofReal B)⁻¹ ^ t)
                  * ((∫⁻ x, f x ∂volume) ^ (1 - t)
                    * (∫⁻ x, g x ∂volume) ^ t) := by ring
            rw [hring, hAa, hBb, one_mul, one_mul]
          calc (∫⁻ x, f x ∂volume) ^ (1 - t) * (∫⁻ x, g x ∂volume) ^ t
              = ENNReal.ofReal C
                * (((ENNReal.ofReal A)⁻¹ * ∫⁻ x, f x ∂volume) ^ (1 - t)
                  * ((ENNReal.ofReal B)⁻¹ * ∫⁻ x, g x ∂volume) ^ t) := hkey2
            _ ≤ ENNReal.ofReal C
                * (ENNReal.ofReal (1 - t)
                  * ((ENNReal.ofReal A)⁻¹ * ∫⁻ x, f x ∂volume)
                  + ENNReal.ofReal t
                    * ((ENNReal.ofReal B)⁻¹ * ∫⁻ x, g x ∂volume)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact ennreal_geom_mean_le_arith_mean2 _ _ ht0 ht1
            _ ≤ ENNReal.ofReal C
                * ((ENNReal.ofReal C)⁻¹ * ∫⁻ x, h x ∂volume) :=
                mul_le_mul_of_nonneg_left hinter (by positivity)
            _ = ∫⁻ x, h x ∂volume := by
                rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hcT, one_mul]

/-- The Prékopa–Leindler property for a measure `μ` on `E`: the integral
inequality holds for every `0 < t < 1` and all measurable `f g h` satisfying
the pointwise geometric-mean bound. -/
private def PLProp (E : Type*) [Add E] [SMul ℝ E] [MeasurableSpace E]
    (μ : Measure E) : Prop :=
  ∀ {t : ℝ} (_ : 0 < t) (_ : t < 1) {f g h : E → ℝ≥0∞},
    Measurable f → Measurable g → Measurable h →
    (∀ x y : E, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) →
    (∫⁻ x, f x ∂μ) ^ (1 - t) * (∫⁻ x, g x ∂μ) ^ t ≤ ∫⁻ x, h x ∂μ

private theorem pl_one_dim : PLProp ℝ volume := by
  intro t ht0 ht1 f g h hf hg hh hfgh
  exact prekopa_leindler_1d_real ht0 ht1 hf hg hh hfgh

/-- Prékopa–Leindler for a product measure from the two factors (Fubini step:
apply the second-factor case to slices, then the first-factor case to the
slice integrals). -/
private theorem pl_prod {E₁ E₂ : Type*} [Add E₁] [SMul ℝ E₁] [Add E₂] [SMul ℝ E₂]
    [MeasurableSpace E₁] [MeasurableSpace E₂]
    {μ₁ : Measure E₁} {μ₂ : Measure E₂} [SFinite μ₂]
    (h₁ : PLProp E₁ μ₁) (h₂ : PLProp E₂ μ₂) :
    PLProp (E₁ × E₂) (μ₁.prod μ₂) := by
  intro t ht0 ht1 f g h hf hg hh hfgh
  set F : E₁ → ℝ≥0∞ := fun x₁ => ∫⁻ x₂, f (x₁, x₂) ∂μ₂
  set G : E₁ → ℝ≥0∞ := fun y₁ => ∫⁻ y₂, g (y₁, y₂) ∂μ₂
  set H : E₁ → ℝ≥0∞ := fun z₁ => ∫⁻ z₂, h (z₁, z₂) ∂μ₂
  have hF : Measurable F := hf.lintegral_prod_right'
  have hG : Measurable G := hg.lintegral_prod_right'
  have hH : Measurable H := hh.lintegral_prod_right'
  have hFGH : ∀ x₁ y₁ : E₁,
      F x₁ ^ (1 - t) * G y₁ ^ t ≤ H ((1 - t) • x₁ + t • y₁) := by
    intro x₁ y₁
    have hfx : Measurable fun u : E₂ => f (x₁, u) :=
      hf.comp (measurable_prodMk_left (x := x₁))
    have hgy : Measurable fun v : E₂ => g (y₁, v) :=
      hg.comp (measurable_prodMk_left (x := y₁))
    have hhz : Measurable fun w : E₂ => h ((1 - t) • x₁ + t • y₁, w) :=
      hh.comp (measurable_prodMk_left (x := (1 - t) • x₁ + t • y₁))
    have hsl := h₂ ht0 ht1 hfx hgy hhz (fun u v => ?_)
    · exact hsl
    · have hCe := hfgh (x₁, u) (y₁, v)
      have harg : (1 - t) • (x₁, u) + t • (y₁, v)
          = ((1 - t) • x₁ + t • y₁, (1 - t) • u + t • v) := by
        rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk]
      rw [harg] at hCe
      exact hCe
  have hmain := h₁ ht0 ht1 hF hG hH hFGH
  rw [show (∫⁻ x₁, F x₁ ∂μ₁) = ∫⁻ z, f z ∂(μ₁.prod μ₂) from
    (lintegral_prod f hf.aemeasurable).symm,
    show (∫⁻ y₁, G y₁ ∂μ₁) = ∫⁻ z, g z ∂(μ₁.prod μ₂) from
    (lintegral_prod g hg.aemeasurable).symm,
    show (∫⁻ z₁, H z₁ ∂μ₁) = ∫⁻ z, h z ∂(μ₁.prod μ₂) from
    (lintegral_prod h hh.aemeasurable).symm] at hmain
  exact hmain

/-- Transport Prékopa–Leindler along a measure-preserving measurable
equivalence that respects affine combinations. -/
private theorem pl_map {E F : Type*} [Add E] [SMul ℝ E] [Add F] [SMul ℝ F]
    [MeasurableSpace E] [MeasurableSpace F]
    {μ : Measure E} {ν : Measure F} (e : E ≃ᵐ F)
    (hmeas : MeasurePreserving e μ ν)
    (hcombo : ∀ (a b : ℝ) (x y : E), e (a • x + b • y) = a • e x + b • e y)
    (hPL : PLProp F ν) : PLProp E μ := by
  intro t ht0 ht1 f g h hf hg hh hfgh
  set F' : F → ℝ≥0∞ := fun X => f (e.symm X)
  set G' : F → ℝ≥0∞ := fun Y => g (e.symm Y)
  set H' : F → ℝ≥0∞ := fun Z => h (e.symm Z)
  have hF' : Measurable F' := hf.comp e.symm.measurable
  have hG' : Measurable G' := hg.comp e.symm.measurable
  have hH' : Measurable H' := hh.comp e.symm.measurable
  have hFGH : ∀ X Y : F,
      F' X ^ (1 - t) * G' Y ^ t ≤ H' ((1 - t) • X + t • Y) := by
    intro X Y
    have hCe := hfgh (e.symm X) (e.symm Y)
    have harg : e.symm ((1 - t) • X + t • Y)
        = (1 - t) • e.symm X + t • e.symm Y := by
      have h1 : e ((1 - t) • e.symm X + t • e.symm Y)
          = (1 - t) • X + t • Y := by
        rw [hcombo]
        simp [e.apply_symm_apply]
      have h2 := congrArg e.symm h1
      rw [e.symm_apply_apply] at h2
      exact h2.symm
    have hH'' : H' ((1 - t) • X + t • Y)
        = h ((1 - t) • e.symm X + t • e.symm Y) := congrArg h harg
    rw [hH'']
    exact hCe
  have hmain := hPL ht0 ht1 hF' hG' hH' hFGH
  have eF : (∫⁻ X, F' X ∂ν) = ∫⁻ x, f x ∂μ := by
    have h1 : ∫⁻ X, F' X ∂ν = ∫⁻ X, F' X ∂(Measure.map e μ) := by
      rw [hmeas.map_eq]
    rw [h1, lintegral_map hF' hmeas.measurable]
    apply lintegral_congr_ae
    filter_upwards with x
    exact congrArg f (e.symm_apply_apply x)
  have eG : (∫⁻ Y, G' Y ∂ν) = ∫⁻ y, g y ∂μ := by
    have h1 : ∫⁻ Y, G' Y ∂ν = ∫⁻ Y, G' Y ∂(Measure.map e μ) := by
      rw [hmeas.map_eq]
    rw [h1, lintegral_map hG' hmeas.measurable]
    apply lintegral_congr_ae
    filter_upwards with x
    exact congrArg g (e.symm_apply_apply x)
  have eH : (∫⁻ Z, H' Z ∂ν) = ∫⁻ z, h z ∂μ := by
    have h1 : ∫⁻ Z, H' Z ∂ν = ∫⁻ Z, H' Z ∂(Measure.map e μ) := by
      rw [hmeas.map_eq]
    rw [h1, lintegral_map hH' hmeas.measurable]
    apply lintegral_congr_ae
    filter_upwards with x
    exact congrArg h (e.symm_apply_apply x)
  rw [eF, eG, eH] at hmain
  exact hmain

/-- Prékopa–Leindler on `Fin n → ℝ` by induction: the base case is a Dirac
measure on a singleton; the step splits off one coordinate. -/
private theorem pl_fin_zero : PLProp (Fin 0 → ℝ) volume := by
  intro t ht0 ht1 f g h hf hg hh hfgh
  have hvol : (volume : Measure (Fin 0 → ℝ))
      = Measure.dirac (0 : Fin 0 → ℝ) := Measure.volume_pi_eq_dirac _
  rw [hvol, lintegral_dirac' _ hf, lintegral_dirac' _ hg, lintegral_dirac' _ hh]
  have harg : (1 - t) • (0 : Fin 0 → ℝ) + t • (0 : Fin 0 → ℝ)
      = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
  have hCe := hfgh (0 : Fin 0 → ℝ) (0 : Fin 0 → ℝ)
  rwa [harg] at hCe

private theorem pl_fin : ∀ n : ℕ, PLProp (Fin n → ℝ) volume
  | 0 => pl_fin_zero
  | n + 1 => by
    have hmeas : MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
        volume (volume.prod volume) :=
      measurePreserving_piFinSuccAbove _ 0
    have hcombo : ∀ (a b : ℝ) (x y : Fin (n + 1) → ℝ),
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 (a • x + b • y)
          = a • MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 x
            + b • MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => ℝ) 0 y := by
      intro a b x y
      simp only [MeasurableEquiv.piFinSuccAbove_apply]
      have hsymm : ∀ z : Fin (n + 1) → ℝ,
          (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) 0).symm z
            = (z 0, Fin.removeNth 0 z) := fun z => rfl
      simp only [hsymm]
      rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq]
      constructor
      · simp only [Pi.add_apply, Pi.smul_apply]
      · funext j
        simp only [Fin.removeNth_apply, Pi.add_apply, Pi.smul_apply]
    exact pl_map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      hmeas hcombo (pl_prod pl_one_dim (pl_fin n))

/-- Prékopa–Leindler on Euclidean space, transported from `Fin n → ℝ`. -/
private theorem pl_euclidean (n : ℕ) :
    PLProp (EuclideanSpace ℝ (Fin n)) volume := by
  intro t ht0 ht1 f g h hf hg hh hfgh
  have hcombo : ∀ (a b : ℝ) (x y : EuclideanSpace ℝ (Fin n)),
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm (a • x + b • y)
        = a • (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm x
          + b • (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm y := by
    intro a b x y
    simp only [MeasurableEquiv.toLp_symm_apply]
    simp
  exact pl_map (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n))
    hcombo (pl_fin n) ht0 ht1 hf hg hh hfgh

/--
**Prékopa–Leindler inequality.** Let $n \ge 0$ and $0 < t < 1$, and let
$f, g, h : \mathbb{R}^n \to [0, \infty]$ be Borel measurable functions on Euclidean space
$\mathbb{R}^n$ such that $f(x)^{1-t} g(y)^t \le h((1-t)x + ty)$ for all $x, y \in \mathbb{R}^n$.
Then, with all integrals taken over $\mathbb{R}^n$ against Lebesgue measure,

$$\Big(\int f(x)\,dx\Big)^{1-t} \Big(\int g(x)\,dx\Big)^{t} \le \int h(x)\,dx.$$

Proves `Wanted` entry `prekopa_leindler`.

Source: A. Prékopa, Acta Sci. Math. 32 (1971), 301–316; H. J. Brascamp and E. Lieb, J. Funct. Anal.
22 (1976), 366–389, DOI 10.1016/0022-1236(76)90004-5.
-/
theorem prekopa_leindler
    {n : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {f g h : EuclideanSpace ℝ (Fin n) → ENNReal}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfgh : ∀ x y : EuclideanSpace ℝ (Fin n),
      ENNReal.rpow (f x) (1 - t) * ENNReal.rpow (g y) t ≤
        h ((1 - t) • x + t • y)) :
    ENNReal.rpow (∫⁻ x, f x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) (1 - t) *
      ENNReal.rpow (∫⁻ x, g x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) t ≤
      ∫⁻ x, h x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hloc : ‹MeasurableSpace (EuclideanSpace ℝ (Fin n))›
      = borel (EuclideanSpace ℝ (Fin n)) := BorelSpace.measurable_eq
  have hglob : WithLp.measurableSpace 2 (Fin n → ℝ)
      = borel (EuclideanSpace ℝ (Fin n)) := BorelSpace.measurable_eq
  have hmeq : ‹MeasurableSpace (EuclideanSpace ℝ (Fin n))›
      = WithLp.measurableSpace 2 (Fin n → ℝ) := hloc.trans hglob.symm
  have hf' : @Measurable _ _ (WithLp.measurableSpace 2 (Fin n → ℝ)) _ f :=
    hmeq ▸ hf
  have hg' : @Measurable _ _ (WithLp.measurableSpace 2 (Fin n → ℝ)) _ g :=
    hmeq ▸ hg
  have hh' : @Measurable _ _ (WithLp.measurableSpace 2 (Fin n → ℝ)) _ h :=
    hmeq ▸ hh
  subst hmeq
  exact pl_euclidean n ht0 ht1 hf' hg' hh' hfgh

end MathlibExt.MeasureTheory.Integral.PrekopaLeindlerWanted
end
