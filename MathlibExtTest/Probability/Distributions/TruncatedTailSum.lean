/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.TruncatedTailSum

/-!
# Tests for the truncated curtate expectation identity

Boundary instantiations of `integral_min_natFloor_eq_sum`, including the
`T = 1` atom separating the nonstrict from the strict tail, and an explicit
finite-distribution pin evaluated independently on both sides.
-/

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Probability.Finance.CurtateTruncationTests

open MathlibExt.Probability.Finance.CurtateTruncation

private theorem ae_nonneg_const {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ᵐ[Measure.dirac (() : Unit)] (fun _ => c) :=
  Filter.Eventually.of_forall fun _ => hc

private theorem dirac_unit_toReal_of_mem {s : Set Unit} (h : () ∈ s) :
    (Measure.dirac () s).toReal = 1 := by
  rw [Measure.dirac_apply, Set.indicator_of_mem h, Pi.one_apply, ENNReal.toReal_one]

private theorem dirac_unit_toReal_of_notMem {s : Set Unit} (h : () ∉ s) :
    (Measure.dirac () s).toReal = 0 := by
  rw [Measure.dirac_apply, Set.indicator_of_notMem h, ENNReal.toReal_zero]

-- T = 1 a.s., n = 1: both sides equal 1.
example : ∫ ω, (min ⌊(fun _ => (1:ℝ)) ω⌋₊ (1:ℕ) : ℝ) ∂(Measure.dirac ()) = 1 := by
  have h := integral_min_natFloor_eq_sum (Measure.dirac ()) (fun _ => (1:ℝ))
    measurable_const (ae_nonneg_const zero_le_one) (1:ℕ)
  rw [h, Finset.Icc_self, Finset.sum_singleton]
  apply dirac_unit_toReal_of_mem
  simp only [Set.mem_ofPred_eq]
  norm_num

-- Strict tail at the atom T = 1: the sum with `<` is 0, pinning the `≥` convention.
example : (∑ k ∈ Finset.Icc (1:ℕ) 1,
    (Measure.dirac () {ω : Unit | (k:ℝ) < (fun _ => (1:ℝ)) ω}).toReal) = 0 := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  apply dirac_unit_toReal_of_notMem
  simp only [Set.mem_ofPred_eq]
  norm_num

-- T = 0 a.s., n = 1: both sides equal 0.
example : ∫ ω, (min ⌊(fun _ => (0:ℝ)) ω⌋₊ (1:ℕ) : ℝ) ∂(Measure.dirac ()) = 0 := by
  have h := integral_min_natFloor_eq_sum (Measure.dirac ()) (fun _ => (0:ℝ))
    measurable_const (ae_nonneg_const le_rfl) (1:ℕ)
  rw [h, Finset.Icc_self, Finset.sum_singleton]
  apply dirac_unit_toReal_of_notMem
  simp only [Set.mem_ofPred_eq]
  norm_num

-- n = 0: both sides equal 0 (empty sum).
example : ∫ ω, (min ⌊(fun _ => (1:ℝ)) ω⌋₊ (0:ℕ) : ℝ) ∂(Measure.dirac ()) = 0 := by
  have h := integral_min_natFloor_eq_sum (Measure.dirac ()) (fun _ => (1:ℝ))
    measurable_const (ae_nonneg_const zero_le_one) (0:ℕ)
  rw [h, Finset.Icc_eq_empty (show ¬ (1:ℕ) ≤ 0 by norm_num), Finset.sum_empty]

-- Fractional T = 2.5 a.s., n = 3: both sides equal 2.
example : ∫ ω, (min ⌊(fun _ => (2.5:ℝ)) ω⌋₊ (3:ℕ) : ℝ) ∂(Measure.dirac ()) = 2 := by
  have h := integral_min_natFloor_eq_sum (Measure.dirac ()) (fun _ => (2.5:ℝ))
    measurable_const (ae_nonneg_const (c := 2.5) (by norm_num)) (3:ℕ)
  rw [h, show Finset.Icc (1:ℕ) 3 = ({1, 2, 3} : Finset ℕ) from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have t1 : (Measure.dirac () {ω : Unit | ((1:ℕ):ℝ) ≤ (fun _ => (2.5:ℝ)) ω}).toReal = 1 :=
    dirac_unit_toReal_of_mem (by simp only [Set.mem_ofPred_eq]; norm_num)
  have t2 : (Measure.dirac () {ω : Unit | ((2:ℕ):ℝ) ≤ (fun _ => (2.5:ℝ)) ω}).toReal = 1 :=
    dirac_unit_toReal_of_mem (by simp only [Set.mem_ofPred_eq]; norm_num)
  have t3 : (Measure.dirac () {ω : Unit | ((3:ℕ):ℝ) ≤ (fun _ => (2.5:ℝ)) ω}).toReal = 0 :=
    dirac_unit_toReal_of_notMem (by simp only [Set.mem_ofPred_eq]; norm_num)
  rw [t1, t2, t3]
  norm_num

-- Atom at the integer date T = 2 a.s., n = 2: both sides equal 2.
example : ∫ ω, (min ⌊(fun _ => (2:ℝ)) ω⌋₊ (2:ℕ) : ℝ) ∂(Measure.dirac ()) = 2 := by
  have h := integral_min_natFloor_eq_sum (Measure.dirac ()) (fun _ => (2:ℝ))
    measurable_const (ae_nonneg_const (c := 2) (by norm_num)) (2:ℕ)
  rw [h, show Finset.Icc (1:ℕ) 2 = ({1, 2} : Finset ℕ) from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have t1 : (Measure.dirac () {ω : Unit | ((1:ℕ):ℝ) ≤ (fun _ => (2:ℝ)) ω}).toReal = 1 :=
    dirac_unit_toReal_of_mem (by simp only [Set.mem_ofPred_eq]; norm_num)
  have t2 : (Measure.dirac () {ω : Unit | ((2:ℕ):ℝ) ≤ (fun _ => (2:ℝ)) ω}).toReal = 1 :=
    dirac_unit_toReal_of_mem (by simp only [Set.mem_ofPred_eq]; norm_num)
  rw [t1, t2]
  norm_num

-- Truncation: T = 7 a.s. with floor above n = 2; both sides equal 2.
example : ∫ ω, (min ⌊(fun _ => (7:ℝ)) ω⌋₊ (2:ℕ) : ℝ) ∂(Measure.dirac ()) = 2 := by
  have h := integral_min_natFloor_eq_sum (Measure.dirac ()) (fun _ => (7:ℝ))
    measurable_const (ae_nonneg_const (c := 7) (by norm_num)) (2:ℕ)
  rw [h, show Finset.Icc (1:ℕ) 2 = ({1, 2} : Finset ℕ) from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have t1 : (Measure.dirac () {ω : Unit | ((1:ℕ):ℝ) ≤ (fun _ => (7:ℝ)) ω}).toReal = 1 :=
    dirac_unit_toReal_of_mem (by simp only [Set.mem_ofPred_eq]; norm_num)
  have t2 : (Measure.dirac () {ω : Unit | ((2:ℕ):ℝ) ≤ (fun _ => (7:ℝ)) ω}).toReal = 1 :=
    dirac_unit_toReal_of_mem (by simp only [Set.mem_ofPred_eq]; norm_num)
  rw [t1, t2]
  norm_num

-- (b) numeric pin: two-point distribution, both sides evaluated independently.
private noncomputable def μb : Measure (Fin 2) :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • Measure.dirac 1

private def Tb : Fin 2 → ℝ := fun i => if i = 0 then 0.5 else 2.5

private theorem hfb_meas : Measurable (fun ω : Fin 2 => (min ⌊Tb ω⌋₊ (2:ℕ) : ℝ)) :=
  measurable_of_countable _

private theorem hfb_int_dirac (a : Fin 2) :
    Integrable (fun ω : Fin 2 => (min ⌊Tb ω⌋₊ (2:ℕ) : ℝ)) (Measure.dirac a) := by
  apply Integrable.of_bound hfb_meas.aestronglyMeasurable 2
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), min_le_iff]
  right
  norm_num

private theorem hfb_int_w (a : Fin 2) :
    Integrable (fun ω : Fin 2 => (min ⌊Tb ω⌋₊ (2:ℕ) : ℝ))
      ((2⁻¹ : ℝ≥0∞) • Measure.dirac a) :=
  (hfb_int_dirac a).smul_measure (by simp)

private theorem hTb0 : Tb 0 = 0.5 := by simp [Tb]

private theorem hTb1 : Tb 1 = 2.5 := by simp [Tb, show (1:Fin 2) ≠ 0 from by decide]

private theorem hfl0 : ⌊(0.5:ℝ)⌋₊ = 0 := by
  rw [Nat.floor_eq_iff (show (0:ℝ) ≤ 0.5 by norm_num)]
  norm_num

private theorem hfl2 : ⌊(2.5:ℝ)⌋₊ = 2 := by
  rw [Nat.floor_eq_iff (show (0:ℝ) ≤ 2.5 by norm_num)]
  norm_num

private theorem hm0 : min (((0:ℕ)):ℝ) (((2:ℕ)):ℝ) = 0 := by
  rw [min_eq_left (by norm_num : ((0:ℕ):ℝ) ≤ ((2:ℕ):ℝ))]
  norm_num

private theorem hm2 : min (((2:ℕ)):ℝ) (((2:ℕ)):ℝ) = 2 := by
  rw [min_eq_left (by norm_num : ((2:ℕ):ℝ) ≤ ((2:ℕ):ℝ))]
  norm_num

private theorem hw : ((2⁻¹ : ℝ≥0∞)).toReal = 1 / 2 := by simp

private theorem hb_lhs : ∫ ω, (min ⌊Tb ω⌋₊ (2:ℕ) : ℝ) ∂μb = 1 := by
  simp only [μb]
  rw [integral_add_measure (hfb_int_w 0) (hfb_int_w 1)]
  simp only [integral_smul_measure, integral_dirac, hTb0, hTb1, hfl0, hfl2,
    hm0, hm2, hw, smul_eq_mul]
  norm_num

private theorem hb_rhs :
    (∑ k ∈ Finset.Icc (1:ℕ) 2, (μb {ω | (k:ℝ) ≤ Tb ω}).toReal) = 1 := by
  rw [show Finset.Icc (1:ℕ) 2 = ({1, 2} : Finset ℕ) from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have m00 : (0:Fin 2) ∉ ({ω : Fin 2 | ((1:ℕ):ℝ) ≤ Tb ω} : Set (Fin 2)) := by
    simp only [Set.mem_ofPred_eq, hTb0]
    norm_num
  have m10 : (1:Fin 2) ∈ ({ω : Fin 2 | ((1:ℕ):ℝ) ≤ Tb ω} : Set (Fin 2)) := by
    simp only [Set.mem_ofPred_eq, hTb1]
    norm_num
  have m02 : (0:Fin 2) ∉ ({ω : Fin 2 | ((2:ℕ):ℝ) ≤ Tb ω} : Set (Fin 2)) := by
    simp only [Set.mem_ofPred_eq, hTb0]
    norm_num
  have m12 : (1:Fin 2) ∈ ({ω : Fin 2 | ((2:ℕ):ℝ) ≤ Tb ω} : Set (Fin 2)) := by
    simp only [Set.mem_ofPred_eq, hTb1]
    norm_num
  have d00 : Measure.dirac (0:Fin 2) {ω : Fin 2 | ((1:ℕ):ℝ) ≤ Tb ω} = 0 := by
    rw [Measure.dirac_apply, Set.indicator_of_notMem m00]
  have d10 : Measure.dirac (1:Fin 2) {ω : Fin 2 | ((1:ℕ):ℝ) ≤ Tb ω} = 1 := by
    rw [Measure.dirac_apply, Set.indicator_of_mem m10, Pi.one_apply]
  have d02 : Measure.dirac (0:Fin 2) {ω : Fin 2 | ((2:ℕ):ℝ) ≤ Tb ω} = 0 := by
    rw [Measure.dirac_apply, Set.indicator_of_notMem m02]
  have d12 : Measure.dirac (1:Fin 2) {ω : Fin 2 | ((2:ℕ):ℝ) ≤ Tb ω} = 1 := by
    rw [Measure.dirac_apply, Set.indicator_of_mem m12, Pi.one_apply]
  have s1 : μb {ω : Fin 2 | ((1:ℕ):ℝ) ≤ Tb ω} = (2⁻¹ : ℝ≥0∞) := by
    simp only [μb, Measure.add_apply, Measure.smul_apply, smul_eq_mul, d00, d10]
    simp
  have s2 : μb {ω : Fin 2 | ((2:ℕ):ℝ) ≤ Tb ω} = (2⁻¹ : ℝ≥0∞) := by
    simp only [μb, Measure.add_apply, Measure.smul_apply, smul_eq_mul, d02, d12]
    simp
  rw [s1, s2, hw]
  norm_num

-- Both sides evaluate independently to 1.
example : (∫ ω, (min ⌊Tb ω⌋₊ (2:ℕ) : ℝ) ∂μb)
    = ∑ k ∈ Finset.Icc (1:ℕ) 2, (μb {ω | (k:ℝ) ≤ Tb ω}).toReal := by
  rw [hb_lhs, hb_rhs]

-- μb is a probability measure (local to these tests).
private instance : IsProbabilityMeasure μb where
  measure_univ := by
    have h0 : Measure.dirac (0 : Fin 2) Set.univ = 1 := by
      rw [Measure.dirac_apply, Set.indicator_of_mem (Set.mem_univ (0 : Fin 2)),
        Pi.one_apply]
    have h1 : Measure.dirac (1 : Fin 2) Set.univ = 1 := by
      rw [Measure.dirac_apply, Set.indicator_of_mem (Set.mem_univ (1 : Fin 2)),
        Pi.one_apply]
    simp only [μb, Measure.add_apply, Measure.smul_apply, smul_eq_mul, h0, h1,
      mul_one]
    exact ENNReal.inv_two_add_inv_two

private theorem hTb_meas : Measurable Tb := measurable_of_countable _

private theorem hTb_nn : 0 ≤ᵐ[μb] Tb :=
  Filter.Eventually.of_forall fun i => by
    by_cases h : i = 0 <;> simp [Tb, h] <;> norm_num

-- Same identity through `integral_min_natFloor_eq_sum` at the non-Dirac μb.
example : (∫ ω, (min ⌊Tb ω⌋₊ (2:ℕ) : ℝ) ∂μb)
    = ∑ k ∈ Finset.Icc (1:ℕ) 2, (μb {ω | (k:ℝ) ≤ Tb ω}).toReal :=
  integral_min_natFloor_eq_sum μb Tb hTb_meas hTb_nn 2

-- Same numeric value through the theorem, with hb_rhs as the pin.
example : (∫ ω, (min ⌊Tb ω⌋₊ (2:ℕ) : ℝ) ∂μb) = 1 := by
  have h := integral_min_natFloor_eq_sum μb Tb hTb_meas hTb_nn (2:ℕ)
  rw [h, hb_rhs]

end MathlibExt.Probability.Finance.CurtateTruncationTests
