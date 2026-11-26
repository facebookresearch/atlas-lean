/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstant

/-! # Haugland's 2016 upper bound for minimum overlap

The rational 95-step certificate is adapted from Georgiev–Gómez-Serrano–Tao–Wagner,
*Mathematical Exploration and Discovery at Scale*. Its heights have denominator `10^8`,
with the center height chosen to make the mass exactly one. Overlaps interpolate linearly
between consecutive grid translations.
-/

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

/-- **Statement of Haugland's 2016 upper bound for the minimum-overlap constant.** The
proposition that the continuous Erdős minimum-overlap constant $C_{1b}$ satisfies
$C_{1b} \le 0.380926$.

Source: Haugland 2016; Optimization Problems, Constant 1b. -/
def upperBound_H2016 : Prop := C₁ᵦ ≤ (380926 : ℝ) / 1000000

private def halfHeights : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50607430, 63204669, 67933280,
   88819386, 88921470, 67823124, 30, 9476437, 1439263, 42393186, 59807361,
   80390961, 68309892, 31474938, 40405948, 85844373, 79650304, 59043315,
   41056218, 27093270, 61338428, 70950165, 58057362, 80353811, 71526388,
   82261133, 80843388, 68353398, 64571901, 88941772, 94338984, 84153696,
   79450522, 94194343, 96222323, 96127075, 99240912]

private def heights : List ℕ := halfHeights.dropLast ++ halfHeights.reverse

private theorem heights_length : heights.length = 95 := by decide

private theorem heights_range : ∀ a ∈ heights, a ≤ 100000000 := by decide

private noncomputable def width : ℝ := 2 / 95

private theorem width_pos : 0 < width := by norm_num [width]

private noncomputable def cell (i : Fin 95) : Set ℝ :=
  Ico ((i : ℝ) * width - 1) (((i : ℝ) + 1) * width - 1)

private noncomputable def amplitude (i : Fin 95) : ℝ :=
  (heights[i.val]?.getD 0 : ℝ) / 100000000

private noncomputable def witness (t : ℝ) : ℝ :=
  ∑ i : Fin 95, (cell i).indicator (fun _ ↦ amplitude i) t

private noncomputable def complement (t : ℝ) : ℝ :=
  continuousSupportInterval.indicator (fun t ↦ 1 - witness t) t

private theorem cell_unique (i j : Fin 95) (t : ℝ)
    (hi : t ∈ cell i) (hj : t ∈ cell j) : i = j := by
  have h₁ : (i : ℝ) < (j : ℝ) + 1 := by
    have := hi.1
    have := hj.2
    dsimp [cell] at *
    nlinarith [width_pos]
  have h₂ : (j : ℝ) < (i : ℝ) + 1 := by
    have := hj.1
    have := hi.2
    dsimp [cell] at *
    nlinarith [width_pos]
  have hi' : i.val < j.val + 1 := by exact_mod_cast h₁
  have hj' : j.val < i.val + 1 := by exact_mod_cast h₂
  apply Fin.ext
  omega

private theorem witness_on_cell (i : Fin 95) (t : ℝ) (ht : t ∈ cell i) :
    witness t = amplitude i := by
  unfold witness
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem ht _
  · intro j _ hji
    have hj : t ∉ cell j := fun hj ↦ hji (cell_unique j i t hj ht)
    exact indicator_of_notMem hj _
  · simp

private theorem cell_cover (t : ℝ) (ht : t ∈ Ico (-1 : ℝ) 1) :
    ∃ i : Fin 95, t ∈ cell i := by
  let u := (t + 1) / width
  have hu : 0 ≤ u := div_nonneg (by linarith [ht.1]) width_pos.le
  have hu' : u < 95 := by
    dsimp [u, width]
    linarith [ht.2]
  have hn : 0 ≤ Int.floor u := Int.floor_nonneg.mpr hu
  have hn' : Int.floor u < 95 := by
    exact Int.floor_lt.mpr hu'
  let i : Fin 95 := ⟨(Int.floor u).toNat, by omega⟩
  refine ⟨i, ?_⟩
  have hi : (i : ℝ) = (Int.floor u : ℝ) := by
    dsimp [i]
    exact_mod_cast Int.toNat_of_nonneg hn
  have hlo := Int.floor_le u
  have hhi := Int.lt_floor_add_one u
  rw [← hi] at hlo hhi
  change (i : ℝ) * width - 1 ≤ t ∧ t < ((i : ℝ) + 1) * width - 1
  constructor
  · have := (le_div_iff₀ width_pos).mp hlo
    linarith
  · have := (div_lt_iff₀ width_pos).mp hhi
    linarith

private theorem amplitude_range (i : Fin 95) : amplitude i ∈ Icc (0 : ℝ) 1 := by
  have hmem : heights[i.val]?.getD 0 ∈ heights := by
    have hi : i.val < heights.length := by rw [heights_length]; exact i.isLt
    simp only [List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have ha := heights_range _ hmem
  dsimp [amplitude]
  constructor
  · positivity
  · apply (div_le_one₀ (by norm_num)).2
    exact_mod_cast ha

private theorem witness_range (t : ℝ) : witness t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : ∃ i : Fin 95, t ∈ cell i
  · obtain ⟨i, hi⟩ := ht
    rw [witness_on_cell i t hi]
    exact amplitude_range i
  · have hz : witness t = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (fun hi ↦ ht ⟨i, hi⟩) _
    rw [hz]
    norm_num

private theorem witness_measurable : Measurable witness := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.indicator measurableSet_Ico

private theorem cell_subset (i : Fin 95) : cell i ⊆ continuousSupportInterval := by
  intro t ht
  have hi : (i : ℝ) + 1 ≤ 95 := by exact_mod_cast i.isLt
  have hi₀ : (0 : ℝ) ≤ i := by positivity
  change -1 ≤ t ∧ t ≤ 1
  dsimp [cell, width] at ht
  constructor <;> linarith [ht.1, ht.2]

private theorem witness_zero (t : ℝ) (ht : t ∉ continuousSupportInterval) :
    witness t = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact indicator_of_notMem (fun hi ↦ ht (cell_subset i hi)) _

private theorem amplitude_mass : (∑ i : Fin 95, amplitude i) = 95 / 2 := by
  have hn : (∑ i : Fin 95, heights[i.val]?.getD 0) = 4750000000 := by decide
  simp only [amplitude]
  rw [← Finset.sum_div, ← Nat.cast_sum, hn]
  norm_num

private theorem cell_integrable (i : Fin 95) (a : ℝ) :
    Integrable ((cell i).indicator (fun _ ↦ a)) :=
  (integrableOn_const measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico

private theorem cell_integral (i : Fin 95) (a : ℝ) :
    (∫ t, (cell i).indicator (fun _ ↦ a) t) = width * a := by
  unfold cell
  rw [integral_indicator_const a measurableSet_Ico, Real.volume_real_Ico, smul_eq_mul]
  rw [show (((i : ℝ) + 1) * width - 1) - ((i : ℝ) * width - 1) = width by ring,
    max_eq_left width_pos.le]

private theorem witness_integral : (∫ t, witness t) = 1 := by
  unfold witness
  rw [integral_finsetSum _ (fun i _ ↦ cell_integrable i (amplitude i))]
  simp_rw [cell_integral]
  rw [← Finset.mul_sum, amplitude_mass]
  norm_num [width]

private theorem witness_admissible : ContinuousAdmissible witness complement := by
  refine ⟨witness_measurable.aemeasurable,
    ((measurable_const.sub witness_measurable).indicator measurableSet_Icc).aemeasurable,
    witness_range, ?_, witness_zero, ?_, ?_, witness_integral⟩
  · intro t
    by_cases ht : t ∈ continuousSupportInterval
    · rw [complement, indicator_of_mem ht]
      constructor <;> linarith [(witness_range t).1, (witness_range t).2]
    · simp [complement, ht]
  · intro t ht
    exact indicator_of_notMem ht _
  · intro t ht
    rw [complement, indicator_of_mem ht]
    ring

private noncomputable def tent (u : ℝ) : ℝ := max (1 - |u|) 0

private theorem tent_interpolate (z : ℤ) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    tent ((z : ℝ) + u) =
      (1 - u) * (if z = 0 then 1 else 0) + u * (if z = -1 then 1 else 0) := by
  by_cases hz : z = 0
  · subst z
    simp [tent, abs_of_nonneg hu, max_eq_left (sub_nonneg.mpr hu')]
  · by_cases hz' : z = -1
    · subst z
      have hneg : (-1 : ℝ) + u ≤ 0 := by linarith
      simp [tent, abs_of_nonpos hneg, max_eq_left hu]
    · have hcases : z ≤ -2 ∨ 1 ≤ z := by omega
      rcases hcases with hneg | hpos
      · have hz₂ : (z : ℝ) ≤ -2 := by exact_mod_cast hneg
        have hzu : (z : ℝ) + u ≤ 0 := by linarith
        have habs : 1 - -((z : ℝ) + u) ≤ 0 := by linarith
        unfold tent
        rw [abs_of_nonpos hzu, max_eq_right habs]
        simp [hz, hz']
      · have hz₁ : (1 : ℝ) ≤ z := by exact_mod_cast hpos
        have hzu : 0 ≤ (z : ℝ) + u := by linarith
        have habs : 1 - ((z : ℝ) + u) ≤ 0 := by linarith
        simp [tent, hz, hz', abs_of_nonneg hzu, max_eq_right habs]

private theorem intersection_length (a b d : ℝ) :
    min (a + d) (b + d) - max a b = d - |a - b| := by
  rcases le_total a b with h | h
  · have hadd : a + d ≤ b + d := by linarith
    rw [min_eq_left hadd, max_eq_right h,
      abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · have hadd : b + d ≤ a + d := by linarith
    rw [min_eq_right hadd, max_eq_left h,
      abs_of_nonneg (sub_nonneg.mpr h)]
    ring

private theorem cell_product (i j : Fin 95) (a b x : ℝ) :
    (fun t ↦ (cell i).indicator (fun _ ↦ a) t *
      (cell j).indicator (fun _ ↦ b) (x + t)) =
    ((cell i) ∩ Ico ((j : ℝ) * width - 1 - x)
      (((j : ℝ) + 1) * width - 1 - x)).indicator (fun _ ↦ a * b) := by
  funext t
  have he : x + t ∈ cell j ↔
      t ∈ Ico ((j : ℝ) * width - 1 - x) (((j : ℝ) + 1) * width - 1 - x) := by
    simp only [cell, mem_Ico, sub_le_iff_le_add, lt_sub_iff_add_lt]
    rw [add_comm t x]
  by_cases hi : t ∈ cell i
  · by_cases hj : x + t ∈ cell j
    · simp [hi, hj, he.mp hj]
    · simp [hi, hj, show t ∉ Ico ((j : ℝ) * width - 1 - x)
        (((j : ℝ) + 1) * width - 1 - x) from fun ht ↦ hj (he.mpr ht)]
  · simp [hi]

private theorem cell_product_integrable (i j : Fin 95) (a b x : ℝ) :
    Integrable (fun t ↦ (cell i).indicator (fun _ ↦ a) t *
      (cell j).indicator (fun _ ↦ b) (x + t)) := by
  rw [cell_product, cell, Ico_inter_Ico]
  exact (integrableOn_const measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico

private theorem cell_product_integral (i j : Fin 95) (a b x : ℝ) :
    (∫ t, (cell i).indicator (fun _ ↦ a) t *
      (cell j).indicator (fun _ ↦ b) (x + t)) =
    width * tent (x / width + (i : ℝ) - (j : ℝ)) * (a * b) := by
  rw [cell_product, cell, Ico_inter_Ico, integral_indicator_const _ measurableSet_Ico,
    Real.volume_real_Ico, smul_eq_mul]
  have hj : ((j : ℝ) + 1) * width - 1 - x = (j : ℝ) * width - 1 - x + width := by ring
  have hi : ((i : ℝ) + 1) * width - 1 = (i : ℝ) * width - 1 + width := by ring
  rw [hi, hj, intersection_length]
  have he : (i : ℝ) * width - 1 - ((j : ℝ) * width - 1 - x) =
      (x / width + (i : ℝ) - (j : ℝ)) * width := by
    field_simp [ne_of_gt width_pos]
    ring
  rw [he, abs_mul, abs_of_pos width_pos]
  have he' : width - |x / width + (i : ℝ) - (j : ℝ)| * width =
      width * (1 - |x / width + (i : ℝ) - (j : ℝ)|) := by ring
  rw [he']
  simp only [tent, mul_max_of_nonneg _ _ width_pos.le, mul_zero]

private noncomputable def stepComplement (t : ℝ) : ℝ :=
  ∑ i : Fin 95, (cell i).indicator (fun _ ↦ 1 - amplitude i) t

private theorem complement_eq_step (t : ℝ) (ht : t ≠ 1) :
    complement t = stepComplement t := by
  by_cases hs : t ∈ continuousSupportInterval
  · have htc : t ∈ Ico (-1 : ℝ) 1 := ⟨hs.1, lt_of_le_of_ne hs.2 ht⟩
    obtain ⟨i, hi⟩ := cell_cover t htc
    rw [complement, indicator_of_mem hs, witness_on_cell i t hi]
    symm
    unfold stepComplement
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem hi _
    · intro j _ hji
      exact indicator_of_notMem (fun hj ↦ hji (cell_unique j i t hj hi)) _
    · simp
  · rw [complement, indicator_of_notMem hs]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact indicator_of_notMem (fun hi ↦ hs (cell_subset i hi)) _

private theorem overlap_formula (x : ℝ) :
    continuousOverlap witness complement x =
      ∑ i : Fin 95, ∑ j : Fin 95,
        width * tent (x / width + (i : ℝ) - (j : ℝ)) *
          (amplitude i * (1 - amplitude j)) := by
  have he : continuousOverlap witness complement x =
      ∫ t, witness t * stepComplement (x + t) := by
    unfold continuousOverlap
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht ↦ by simp [continuousOverlapIntegrand, witness_zero t ht])]
    apply integral_congr_ae
    have hae : ∀ᵐ t : ℝ, t ≠ 1 - x := by
      rw [ae_iff]
      simp
    filter_upwards [hae] with t ht
    dsimp [continuousOverlapIntegrand]
    rw [complement_eq_step (x + t) (by intro h; apply ht; linarith)]
  rw [he]
  simp only [witness, stepComplement]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦
    integrable_finsetSum _ (fun j _ ↦ cell_product_integrable i j _ _ x))]
  simp_rw [integral_finsetSum _ (fun j _ ↦ cell_product_integrable _ j _ _ x),
    cell_product_integral]

private def complementNumerator (z : ℤ) : ℕ :=
  if 0 ≤ z ∧ z < 95 then 100000000 - heights[z.toNat]?.getD 0 else 0

private def discreteNumerator (k : ℤ) : ℕ :=
  ∑ i : Fin 95, heights[i.val]?.getD 0 * complementNumerator ((i : ℤ) + k)

private theorem discrete_certificate :
    ∀ k : Fin 191,
      2 * 1000000 * discreteNumerator ((k : ℤ) - 95) ≤
        380926 * 95 * 100000000 ^ 2 := by decide +kernel

private noncomputable def discreteScore (k : ℤ) : ℝ :=
  ∑ i : Fin 95, amplitude i * ((complementNumerator ((i : ℤ) + k) : ℝ) / 100000000)

private theorem discreteScore_eq (k : ℤ) :
    discreteScore k = (discreteNumerator k : ℝ) / (100000000 * 100000000) := by
  simp only [discreteScore, amplitude, div_mul_div_comm]
  rw [← Finset.sum_div]
  simp only [discreteNumerator, Nat.cast_sum, Nat.cast_mul]

private theorem complementNumerator_at (i : Fin 95) :
    (complementNumerator (i : ℤ) : ℝ) / 100000000 = 1 - amplitude i := by
  have hmem : heights[i.val]?.getD 0 ∈ heights := by
    have hi : i.val < heights.length := by rw [heights_length]; exact i.isLt
    simp only [List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have ha := heights_range _ hmem
  have hi₀ : (0 : ℤ) ≤ i := by positivity
  have hi₁ : (i : ℤ) < 95 := by exact_mod_cast i.isLt
  simp only [complementNumerator, hi₀, hi₁, and_self, ite_true, Int.toNat_natCast,
    Nat.cast_sub ha, amplitude]
  norm_num
  ring

private theorem diagonal_sum (i : Fin 95) (k : ℤ) :
    (∑ j : Fin 95, (1 - amplitude j) * (if (i : ℤ) + k = j then 1 else 0)) =
      (complementNumerator ((i : ℤ) + k) : ℝ) / 100000000 := by
  by_cases h : 0 ≤ (i : ℤ) + k ∧ (i : ℤ) + k < 95
  · let j : Fin 95 := ⟨((i : ℤ) + k).toNat, by omega⟩
    have hj : (j : ℤ) = (i : ℤ) + k := Int.toNat_of_nonneg h.1
    rw [Finset.sum_eq_single j]
    · rw [← hj, complementNumerator_at]
      simp
    · intro j' _ hne
      have hneq : (i : ℤ) + k ≠ (j' : ℤ) := by
        intro he
        apply hne
        apply Fin.ext
        exact_mod_cast he.symm.trans hj.symm
      simp [hneq]
    · simp
  · have hz : complementNumerator ((i : ℤ) + k) = 0 := by simp [complementNumerator, h]
    rw [hz]
    norm_num
    apply Finset.sum_eq_zero
    intro j _
    have hneq : (i : ℤ) + k ≠ j := by
      intro he
      apply h
      rw [he]
      exact ⟨by positivity, by exact_mod_cast j.isLt⟩
    simp [hneq]

private theorem discreteScore_bound (k : ℤ) :
    width * discreteScore k ≤ (380926 : ℝ) / 1000000 := by
  by_cases h : -95 ≤ k ∧ k ≤ 95
  · let j : Fin 191 := ⟨(k + 95).toNat, by omega⟩
    have hj : (j : ℤ) - 95 = k := by
      have hj' : (j : ℤ) = k + 95 := Int.toNat_of_nonneg (by omega)
      omega
    have hn := discrete_certificate j
    rw [hj] at hn
    have hr : (2 : ℝ) * 1000000 * (discreteNumerator k : ℝ) ≤
        380926 * 95 * 100000000 ^ 2 := by exact_mod_cast hn
    rw [discreteScore_eq]
    generalize hv : (discreteNumerator k : ℝ) = v at hr ⊢
    norm_num [width] at hr ⊢
    linarith
  · have hz : discreteNumerator k = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi₀ : (0 : ℤ) ≤ i := by positivity
      have hi₁ : (i : ℤ) < 95 := by exact_mod_cast i.isLt
      have hout : ¬(0 ≤ (i : ℤ) + k ∧ (i : ℤ) + k < 95) := by omega
      simp [complementNumerator, hout]
    rw [discreteScore_eq, hz]
    norm_num

private theorem tent_grid (x u : ℝ) (k : ℤ) (i j : Fin 95)
    (he : x / width = (k : ℝ) + u) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    tent (x / width + (i : ℝ) - (j : ℝ)) =
      (1 - u) * (if (i : ℤ) + k = j then 1 else 0) +
        u * (if (i : ℤ) + (k + 1) = j then 1 else 0) := by
  have harg : x / width + (i : ℝ) - (j : ℝ) =
      (((i : ℤ) + k - (j : ℤ) : ℤ) : ℝ) + u := by
    rw [he]
    push_cast
    ring
  rw [harg, tent_interpolate _ u hu hu']
  have h₀ : ((i : ℤ) + k - (j : ℤ) = 0) ↔ (i : ℤ) + k = j := by omega
  have h₁ : ((i : ℤ) + k - (j : ℤ) = -1) ↔ (i : ℤ) + (k + 1) = j := by omega
  simp only [h₀, h₁]

private theorem witness_overlap_bound (x : ℝ) :
    continuousOverlap witness complement x ≤ (380926 : ℝ) / 1000000 := by
  let k := Int.floor (x / width)
  let u := x / width - (k : ℝ)
  have he : x / width = (k : ℝ) + u := by dsimp [u]; ring
  have hu : 0 ≤ u := sub_nonneg.mpr (Int.floor_le _)
  have hu' : u ≤ 1 := by
    have hfloor : x / width < (k : ℝ) + 1 := Int.lt_floor_add_one _
    unfold u
    linarith only [hfloor]
  have hterm (i j : Fin 95) :
      width * tent (x / width + (i : ℝ) - (j : ℝ)) *
        (amplitude i * (1 - amplitude j)) =
      ((1 - u) * width * amplitude i) *
        ((1 - amplitude j) * (if (i : ℤ) + k = j then 1 else 0)) +
      (u * width * amplitude i) *
        ((1 - amplitude j) * (if (i : ℤ) + (k + 1) = j then 1 else 0)) := by
    rw [tent_grid x u k i j he hu hu']
    ring
  have hscore : continuousOverlap witness complement x =
      (1 - u) * (width * discreteScore k) + u * (width * discreteScore (k + 1)) := by
    rw [overlap_formula]
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, diagonal_sum]
    simp_rw [mul_assoc]
    simp_rw [← Finset.mul_sum]
    rfl
  rw [hscore]
  calc
    _ ≤ (1 - u) * ((380926 : ℝ) / 1000000) + u * ((380926 : ℝ) / 1000000) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (discreteScore_bound k) (sub_nonneg.mpr hu'))
        (mul_le_mul_of_nonneg_left (discreteScore_bound (k + 1)) hu)
    _ = (380926 : ℝ) / 1000000 := by ring

/-- **Haugland's 2016 upper bound for the minimum-overlap constant.** The continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 0.380926$.

Source: Haugland 2016 and Optimization Problems 1b. -/
public theorem upperBound_H2016_holds : upperBound_H2016 := by
  refine le_trans (continuousMinimumOverlapConstant_isUniversalLowerBound
    witness complement witness_admissible) ?_
  apply csSup_le (continuousOverlapValues_nonempty witness complement)
  rintro y ⟨x, _, rfl⟩
  exact witness_overlap_bound x

end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted
