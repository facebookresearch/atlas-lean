/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

/-- **AlphaEvolve upper bound for the minimum-overlap constant (statement).** The statement that
the continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 0.380924$.

Source: Georgiev--Gómez-Serrano--Tao--Wagner 2025; Optimization Problems, Constant 1b. -/
def upperBound_GGSWT2025_AlphaEvolve : Prop := C₁ᵦ ≤ (380924 : ℝ) / 1000000

private def heights : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 506074, 632047, 679333, 888194, 889215, 678231, 0, 94764,
  14393, 423932, 598074, 803910, 683099, 314749, 404059, 858444, 796503, 590433, 410562, 270933,
  613384, 709502, 580574, 803538, 715264, 822611, 808434, 683534, 645719, 889418, 943390, 841537,
  794505, 941943, 962223, 961271, 992408, 961271, 962223, 941943, 794505, 841537, 943390, 889418,
  645719, 683534, 808434, 822611, 715264, 803538, 580574, 709502, 613384, 270933, 410562, 590433,
  796503, 858444, 404059, 314749, 683099, 803910, 598074, 423932, 14393, 94764, 0, 678231,
  889215, 888194, 679333, 632047, 506074, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def numerator (i : Fin 95) : ℕ := heights[i.val]!

private theorem numerator_bounds : ∀ i : Fin 95, numerator i ≤ 1000000 := by
  decide +kernel

private theorem numerator_sum : (∑ i : Fin 95, numerator i) = 47500000 := by
  decide +kernel

private noncomputable def coefficient (i : Fin 95) : ℝ := (numerator i : ℝ) / 1000000

private theorem coefficient_bounds (i : Fin 95) : coefficient i ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  · apply (div_le_one (by norm_num : (0 : ℝ) < 1000000)).2
    exact_mod_cast numerator_bounds i

private theorem coefficient_sum : (∑ i : Fin 95, coefficient i) = 95 / 2 := by
  simp only [coefficient, ← Finset.sum_div, ← Nat.cast_sum, numerator_sum]
  norm_num

private noncomputable def left (i : Fin 95) : ℝ := -1 + 2 * (i.val : ℝ) / 95

private noncomputable def bin (i : Fin 95) : Set ℝ := Ico (left i) (left i + 2 / 95)

private noncomputable def witnessF (t : ℝ) : ℝ :=
  ∑ i : Fin 95, (bin i).indicator (fun _ => coefficient i) t

private noncomputable def witnessG (t : ℝ) : ℝ :=
  (Icc (-1 : ℝ) 1).indicator (fun t => 1 - witnessF t) t

private theorem bin_subset (i : Fin 95) : bin i ⊆ Ico (-1 : ℝ) 1 := by
  intro t ht
  have hi₀ : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hi₁ : (i.val : ℝ) ≤ 94 := by exact_mod_cast (by omega : i.val ≤ 94)
  dsimp [bin, left] at ht
  constructor <;> linarith [ht.1, ht.2]

private theorem bin_disjoint (i j : Fin 95) (hij : i ≠ j) : Disjoint (bin i) (bin j) := by
  apply Set.disjoint_left.mpr
  intro t hi hj
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hij' with h | h
  · have h' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (by omega : i.val + 1 ≤ j.val)
    dsimp [bin, left] at hi hj
    linarith [hi.2, hj.1]
  · have h' : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast (by omega : j.val + 1 ≤ i.val)
    dsimp [bin, left] at hi hj
    linarith [hj.2, hi.1]

private theorem witnessF_on_bin (i : Fin 95) (t : ℝ) (ht : t ∈ bin i) :
    witnessF t = coefficient i := by
  unfold witnessF
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem ht _
  · intro j _ hji
    have hj : t ∉ bin j := fun hj => Set.disjoint_left.mp (bin_disjoint i j hji.symm) ht hj
    exact Set.indicator_of_notMem hj _
  · simp

private theorem witnessF_outside (t : ℝ) (ht : t ∉ Ico (-1 : ℝ) 1) : witnessF t = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact Set.indicator_of_notMem (fun hi => ht (bin_subset i hi)) _

private theorem bins_cover (t : ℝ) (ht : t ∈ Ico (-1 : ℝ) 1) : ∃ i : Fin 95, t ∈ bin i := by
  let u : ℝ := (t + 1) * 95 / 2
  have hu₀ : 0 ≤ u := by dsimp [u]; linarith [ht.1]
  have hu₁ : u < 95 := by dsimp [u]; linarith [ht.2]
  have hi : Nat.floor u < 95 := (Nat.floor_lt hu₀).2 hu₁
  let i : Fin 95 := ⟨Nat.floor u, hi⟩
  refine ⟨i, ?_⟩
  have hlo := Nat.floor_le hu₀
  have hhi := Nat.lt_floor_add_one u
  dsimp [bin, left, i, u] at *
  constructor <;> linarith

private theorem witnessF_bounds (t : ℝ) : witnessF t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : t ∈ Ico (-1 : ℝ) 1
  · obtain ⟨i, hi⟩ := bins_cover t ht
    rw [witnessF_on_bin i t hi]
    exact coefficient_bounds i
  · rw [witnessF_outside t ht]
    norm_num

private theorem integral_witnessF : (∫ t, witnessF t) = 1 := by
  have hi (i : Fin 95) : Integrable ((bin i).indicator (fun _ => coefficient i)) :=
    (integrableOn_const (s := bin i) measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico
  unfold witnessF
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [integral_indicator_const _ measurableSet_Ico, bin, Real.volume_real_Ico,
    add_sub_cancel_left, max_eq_left (by norm_num : (0 : ℝ) ≤ 2 / 95), smul_eq_mul]
  rw [← Finset.mul_sum, coefficient_sum]
  norm_num

private theorem witness_admissible :
    ContinuousAdmissible witnessF witnessG := by
  have hm : Measurable witnessF :=
    Finset.measurable_sum _ (fun i _ => measurable_const.indicator measurableSet_Ico)
  have hg : Measurable witnessG :=
    (measurable_const.sub hm).indicator measurableSet_Icc
  refine ⟨hm.aemeasurable, hg.aemeasurable, witnessF_bounds, ?_, ?_, ?_, ?_, integral_witnessF⟩
  · intro t
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · rw [witnessG, Set.indicator_of_mem ht]
      have hf := witnessF_bounds t
      constructor <;> linarith [hf.1, hf.2]
    · rw [witnessG, Set.indicator_of_notMem ht]
      norm_num
  · intro t ht
    apply witnessF_outside t
    exact fun h => ht ⟨h.1, h.2.le⟩
  · intro t ht
    exact Set.indicator_of_notMem ht _
  · intro t ht
    change t ∈ Icc (-1 : ℝ) 1 at ht
    rw [witnessG, Set.indicator_of_mem ht]
    ring

private def complementNumerator (j : ℤ) : ℕ :=
  if 0 ≤ j ∧ j < 95 then 1000000 - heights[j.toNat]! else 0

private def fullGridNumerator (k : ℤ) : ℕ :=
  ∑ i : Fin 95, numerator i * complementNumerator ((i.val : ℤ) + k)

private theorem full_grid_certificate : ∀ p : Fin 191,
    2 * fullGridNumerator ((p.val : ℤ) - 95) * 1000000 ≤
      380924 * 95 * 1000000 ^ 2 := by
  decide +kernel

private theorem full_grid_bound (k : ℤ) :
    2 * fullGridNumerator k * 1000000 ≤ 380924 * 95 * 1000000 ^ 2 := by
  by_cases hk : -95 ≤ k ∧ k ≤ 95
  · let p : Fin 191 := ⟨(k + 95).toNat, by omega⟩
    have hp : (p.val : ℤ) - 95 = k := by dsimp [p]; omega
    simpa only [hp] using full_grid_certificate p
  · have hzero : fullGridNumerator k = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hout : ¬ (0 ≤ (i.val : ℤ) + k ∧ (i.val : ℤ) + k < 95) := by omega
      simp [complementNumerator, hout]
    rw [hzero]
    norm_num

private noncomputable def gridReal (k : ℤ) : ℝ :=
  ∑ i : Fin 95, coefficient i * ((complementNumerator ((i.val : ℤ) + k) : ℝ) / 1000000)

private theorem gridReal_eq (k : ℤ) :
    gridReal k = (fullGridNumerator k : ℝ) / 1000000 ^ 2 := by
  unfold gridReal fullGridNumerator coefficient
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_mul]
  ring

private theorem gridReal_bound (k : ℤ) :
    (2 / 95) * gridReal k ≤ (380924 : ℝ) / 1000000 := by
  rw [gridReal_eq]
  have h : (2 : ℝ) * fullGridNumerator k * 1000000 ≤
      380924 * 95 * 1000000 ^ 2 := by exact_mod_cast full_grid_bound k
  linarith

private theorem complement_sum (i : Fin 95) (k : ℤ) :
    (∑ j : Fin 95, (1 - coefficient j) *
      (if (j.val : ℤ) = (i.val : ℤ) + k then 1 else 0)) =
        (complementNumerator ((i.val : ℤ) + k) : ℝ) / 1000000 := by
  by_cases hk : 0 ≤ (i.val : ℤ) + k ∧ (i.val : ℤ) + k < 95
  · let j : Fin 95 := ⟨((i.val : ℤ) + k).toNat, by omega⟩
    have hj : (j.val : ℤ) = (i.val : ℤ) + k := by dsimp [j]; omega
    rw [Finset.sum_eq_single j]
    · rw [ite_eq_left hj, mul_one, complementNumerator, ite_eq_left hk]
      change 1 - coefficient j = ((1000000 - numerator j : ℕ) : ℝ) / 1000000
      rw [Nat.cast_sub (numerator_bounds j)]
      unfold coefficient
      norm_num
      ring
    · intro j' _ hne
      have hne' : (j'.val : ℤ) ≠ (i.val : ℤ) + k := by
        intro he
        apply hne
        apply Fin.ext
        omega
      simp [hne']
    · simp
  · rw [complementNumerator, ite_eq_right hk, Nat.cast_zero, zero_div]
    apply Finset.sum_eq_zero
    intro j _
    have hne : (j.val : ℤ) ≠ (i.val : ℤ) + k := by omega
    simp [hne]

private noncomputable def hat (x : ℝ) : ℝ := max (1 - |x|) 0

private theorem hat_interpolation (k m : ℤ) (u : ℝ) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) :
    hat ((k : ℝ) + u - m) =
      (1 - u) * (if m = k then 1 else 0) + u * (if m = k + 1 then 1 else 0) := by
  by_cases h₀ : m = k
  · subst m
    simp [hat, abs_of_nonneg hu₀, max_eq_left (sub_nonneg.mpr hu₁)]
  by_cases h₁ : m = k + 1
  · subst m
    have hk : k + 1 ≠ k := by omega
    simp only [hk, ↓reduceIte, Int.cast_add, Int.cast_one, mul_zero, mul_one, zero_add]
    have he : (k : ℝ) + u - ((k : ℝ) + 1) = u - 1 := by ring
    rw [he, hat, abs_of_nonpos (sub_nonpos.mpr hu₁)]
    have he' : 1 - -(u - 1) = u := by ring
    rw [he', max_eq_left hu₀]
  simp only [h₀, h₁, ↓reduceIte, mul_zero, zero_add]
  rcases le_total m k with h | h
  · have h' : m + 1 ≤ k := by omega
    have hc : (m : ℝ) + 1 ≤ k := by exact_mod_cast h'
    have hz : 1 ≤ (k : ℝ) + u - m := by linarith
    rw [hat, abs_of_nonneg (by linarith), max_eq_right (by linarith)]
  · have h' : k + 2 ≤ m := by omega
    have hc : (k : ℝ) + 2 ≤ m := by exact_mod_cast h'
    have hz : (k : ℝ) + u - m ≤ -1 := by linarith
    rw [hat, abs_of_nonpos (by linarith), max_eq_right (by linarith)]

private theorem interval_length (a b x : ℝ) :
    max (min (a + 2 / 95) (b + 2 / 95 - x) - max a (b - x)) 0 =
      (2 / 95) * hat ((95 / 2) * (x + a - b)) := by
  by_cases hz : 0 ≤ x + a - b
  · have hab : b - x ≤ a := by linarith
    have hab' : b + 2 / 95 - x ≤ a + 2 / 95 := by linarith
    rw [min_eq_right hab', max_eq_left hab, hat,
      abs_of_nonneg (mul_nonneg (by norm_num) hz)]
    by_cases h : x + a - b ≤ 2 / 95
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      ring
  · have hz' : x + a - b ≤ 0 := le_of_not_ge hz
    have hab : a ≤ b - x := by linarith
    have hab' : a + 2 / 95 ≤ b + 2 / 95 - x := by linarith
    rw [min_eq_left hab', max_eq_right hab, hat,
      abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hz')]
    by_cases h : -(2 / 95) ≤ x + a - b
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      ring


private noncomputable def complementStep (t : ℝ) : ℝ :=
  ∑ i : Fin 95, (bin i).indicator (fun _ => 1 - coefficient i) t

private theorem complementStep_on_bin (i : Fin 95) (t : ℝ) (ht : t ∈ bin i) :
    complementStep t = 1 - coefficient i := by
  unfold complementStep
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem ht _
  · intro j _ hji
    have hj : t ∉ bin j := fun hj => Set.disjoint_left.mp (bin_disjoint i j hji.symm) ht hj
    exact Set.indicator_of_notMem hj _
  · simp

private theorem witnessG_eq (t : ℝ) (hne : t ≠ 1) : witnessG t = complementStep t := by
  by_cases ht : t ∈ Ico (-1 : ℝ) 1
  · obtain ⟨i, hi⟩ := bins_cover t ht
    rw [witnessG, Set.indicator_of_mem (show t ∈ Icc (-1 : ℝ) 1 from ⟨ht.1, ht.2.le⟩),
      witnessF_on_bin i t hi, complementStep_on_bin i t hi]
  · have hout : t ∉ Icc (-1 : ℝ) 1 := by
      intro h
      apply ht
      exact ⟨h.1, lt_of_le_of_ne h.2 hne⟩
    rw [witnessG, Set.indicator_of_notMem hout]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact Set.indicator_of_notMem (fun hi => ht (bin_subset i hi)) _

private noncomputable def overlapAtom (i j : Fin 95) (x : ℝ) : ℝ → ℝ :=
  (Ico (max (left i) (left j - x)) (min (left i + 2 / 95) (left j + 2 / 95 - x))).indicator
    (fun _ => coefficient i * (1 - coefficient j))

private theorem overlapAtom_eq (i j : Fin 95) (x t : ℝ) :
    overlapAtom i j x t =
      (bin i).indicator (fun _ => coefficient i) t *
        (bin j).indicator (fun _ => 1 - coefficient j) (x + t) := by
  have hm : t ∈ Ico (max (left i) (left j - x))
      (min (left i + 2 / 95) (left j + 2 / 95 - x)) ↔
        t ∈ bin i ∧ x + t ∈ bin j := by
    simp only [mem_Ico, bin, max_le_iff, lt_min_iff]
    constructor
    · intro h
      exact ⟨⟨h.1.1, h.2.1⟩, ⟨by linarith [h.1.2], by linarith [h.2.2]⟩⟩
    · intro h
      exact ⟨⟨h.1.1, by linarith [h.2.1]⟩, ⟨h.1.2, by linarith [h.2.2]⟩⟩
  by_cases hi : t ∈ bin i <;> by_cases hj : x + t ∈ bin j <;>
    simp [overlapAtom, hm, hi, hj]

private theorem overlapAtom_integrable (i j : Fin 95) (x : ℝ) :
    Integrable (overlapAtom i j x) :=
  (integrableOn_const measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico

private theorem integral_overlapAtom (i j : Fin 95) (x : ℝ) :
    (∫ t, overlapAtom i j x t) = (2 / 95) * coefficient i * (1 - coefficient j) *
      hat ((95 / 2) * x + (i.val : ℝ) - j.val) := by
  unfold overlapAtom
  rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico, smul_eq_mul,
    interval_length]
  have he : (95 / 2) * (x + left i - left j) =
      (95 / 2) * x + (i.val : ℝ) - j.val := by unfold left; ring
  rw [he]
  ring

private theorem overlap_expansion (x : ℝ) :
    continuousOverlap witnessF witnessG x =
      ∑ i : Fin 95, ∑ j : Fin 95,
        (2 / 95) * coefficient i * (1 - coefficient j) *
          hat ((95 / 2) * x + (i.val : ℝ) - j.val) := by
  have hz (t : ℝ) (ht : t ∉ continuousSupportInterval) :
      continuousOverlapIntegrand witnessF witnessG x t = 0 := by
    simp [continuousOverlapIntegrand, witness_admissible.zero_outside_f t ht]
  have he : (fun t => continuousOverlapIntegrand witnessF witnessG x t) =ᵐ[volume]
      (fun t => ∑ i : Fin 95, ∑ j : Fin 95, overlapAtom i j x t) := by
    have hne : ∀ᵐ t : ℝ, t ≠ 1 - x := by simp [ae_iff]
    filter_upwards [hne] with t ht
    have hxt : x + t ≠ 1 := by intro h; apply ht; linarith
    rw [continuousOverlapIntegrand, witnessG_eq _ hxt]
    unfold witnessF complementStep
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (overlapAtom_eq i j x t).symm
  unfold continuousOverlap
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz, integral_congr_ae he,
    integral_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => overlapAtom_integrable i j x))]
  simp_rw [integral_finsetSum _ (fun j _ => overlapAtom_integrable _ j x), integral_overlapAtom]

private theorem weighted_grid_sum (v : ℝ) (k : ℤ) :
    (∑ i : Fin 95, ∑ j : Fin 95,
      (2 / 95) * coefficient i * (1 - coefficient j) *
        (v * (if (j.val : ℤ) = (i.val : ℤ) + k then 1 else 0))) =
      (2 / 95) * v * gridReal k := by
  unfold gridReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (2 / 95) * v * coefficient i *
        ∑ j : Fin 95, (1 - coefficient j) *
          (if (j.val : ℤ) = (i.val : ℤ) + k then 1 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [complement_sum]; ring

private theorem overlap_bound (x : ℝ) :
    continuousOverlap witnessF witnessG x ≤ (380924 : ℝ) / 1000000 := by
  let y : ℝ := (95 / 2) * x
  let k : ℤ := Int.floor y
  let u : ℝ := y - k
  have hu₀ : 0 ≤ u := by dsimp [u, k]; exact sub_nonneg.mpr (Int.floor_le y)
  have hu₁ : u ≤ 1 := by
    have h : y < (k : ℝ) + 1 := Int.lt_floor_add_one y
    have he : u + (k : ℝ) = y := by dsimp only [u]; ring
    linarith only [h, he]
  have hhat (i j : Fin 95) :
      hat ((95 / 2) * x + (i.val : ℝ) - j.val) =
        (1 - u) * (if (j.val : ℤ) = (i.val : ℤ) + k then 1 else 0) +
          u * (if (j.val : ℤ) = (i.val : ℤ) + (k + 1) then 1 else 0) := by
    have he : (95 / 2) * x + (i.val : ℝ) - j.val =
        (k : ℝ) + u - (((j.val : ℤ) - i.val : ℤ) : ℝ) := by
      simp only [Int.cast_sub, Int.cast_natCast]
      dsimp [u, y]
      ring
    rw [he, hat_interpolation k ((j.val : ℤ) - i.val) u hu₀ hu₁]
    have h₀ : (j.val : ℤ) - i.val = k ↔ (j.val : ℤ) = (i.val : ℤ) + k := by omega
    have h₁ : (j.val : ℤ) - i.val = k + 1 ↔
        (j.val : ℤ) = (i.val : ℤ) + (k + 1) := by omega
    simp only [h₀, h₁]
  rw [overlap_expansion]
  simp_rw [hhat, mul_add, Finset.sum_add_distrib]
  rw [weighted_grid_sum (1 - u) k, weighted_grid_sum u (k + 1)]
  calc
    _ = (1 - u) * ((2 / 95) * gridReal k) +
        u * ((2 / 95) * gridReal (k + 1)) := by ring
    _ ≤ (1 - u) * ((380924 : ℝ) / 1000000) +
        u * ((380924 : ℝ) / 1000000) :=
      add_le_add (mul_le_mul_of_nonneg_left (gridReal_bound k) (sub_nonneg.mpr hu₁))
        (mul_le_mul_of_nonneg_left (gridReal_bound (k + 1)) hu₀)
    _ = _ := by ring

/-- **AlphaEvolve upper bound for the minimum-overlap constant.** The continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 0.380924$.

Source: Georgiev--Gómez-Serrano--Tao--Wagner 2025 and Optimization Problems 1b. -/
public theorem upperBound_GGSWT2025_AlphaEvolve_holds :
  upperBound_GGSWT2025_AlphaEvolve := by
  refine le_trans (continuousMinimumOverlapConstant_isUniversalLowerBound
    witnessF witnessG witness_admissible) ?_
  apply csSup_le (continuousOverlapValues_nonempty witnessF witnessG)
  rintro y ⟨x, _, rfl⟩
  exact overlap_bound x

end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted
