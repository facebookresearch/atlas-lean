/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.SLE.Defs

open scoped UpperHalfPlane NNReal
open Complex Filter Topology

namespace StatMech.SLE













def crossRatio {K : Type*} [Field K] (z₁ z₂ z₃ z₄ : K) : K :=
  (z₁ - z₃) * (z₂ - z₄) / ((z₁ - z₄) * (z₂ - z₃))




lemma crossRatio_def {K : Type*} [Field K] (z₁ z₂ z₃ z₄ : K) :
    crossRatio z₁ z₂ z₃ z₄ = (z₁ - z₃) * (z₂ - z₄) / ((z₁ - z₄) * (z₂ - z₃)) := rfl







@[simp] lemma crossRatio_self_left_third {K : Type*} [Field K]
    (z z₂ z₄ : K) : crossRatio z z₂ z z₄ = 0 := by
  simp [crossRatio]


@[simp] lemma crossRatio_self_second_fourth {K : Type*} [Field K]
    (z₁ z z₃ : K) : crossRatio z₁ z z₃ z = 0 := by
  simp [crossRatio]




lemma crossRatio_eq_one_of_third_eq_fourth {K : Type*} [Field K]
    {z₁ z₂ z₃ z₄ : K} (h : z₃ = z₄) (h₁ : z₁ - z₄ ≠ 0) (h₂ : z₂ - z₃ ≠ 0) :
    crossRatio z₁ z₂ z₃ z₄ = 1 := by
  subst h
  rw [crossRatio]
  exact div_self (mul_ne_zero h₁ h₂)














structure Mobius (K : Type*) [Field K] where
  
  a : K
  
  b : K
  
  c : K
  
  d : K
  
  det_ne_zero : a * d - b * c ≠ 0



def Mobius.apply {K : Type*} [Field K] (m : Mobius K) (z : K) : K :=
  (m.a * z + m.b) / (m.c * z + m.d)


def Mobius.id (K : Type*) [Field K] : Mobius K where
  a := 1; b := 0; c := 0; d := 1
  det_ne_zero := by simp

@[simp] lemma Mobius.id_apply {K : Type*} [Field K] (z : K) :
    (Mobius.id K).apply z = z := by simp [Mobius.apply, Mobius.id]





lemma crossRatio_translation_invariant {K : Type*} [Field K]
    (t z₁ z₂ z₃ z₄ : K) :
    crossRatio (z₁ + t) (z₂ + t) (z₃ + t) (z₄ + t) = crossRatio z₁ z₂ z₃ z₄ := by
  simp only [crossRatio]
  ring_nf



lemma crossRatio_scaling_invariant {K : Type*} [Field K]
    {s : K} (hs : s ≠ 0) (z₁ z₂ z₃ z₄ : K) :
    crossRatio (s * z₁) (s * z₂) (s * z₃) (s * z₄) = crossRatio z₁ z₂ z₃ z₄ := by
  simp only [crossRatio]
  rw [show s * z₁ - s * z₃ = s * (z₁ - z₃) by ring,
    show s * z₂ - s * z₄ = s * (z₂ - z₄) by ring,
    show s * z₁ - s * z₄ = s * (z₁ - z₄) by ring,
    show s * z₂ - s * z₃ = s * (z₂ - z₃) by ring]
  rw [mul_mul_mul_comm s (z₁ - z₃) s (z₂ - z₄),
    mul_mul_mul_comm s (z₁ - z₄) s (z₂ - z₃)]
  rw [mul_div_mul_left _ _ (mul_ne_zero hs hs)]















noncomputable def cardyPrefactor : ℝ :=
  3 * Real.Gamma (2 / 3) / (Real.Gamma (1 / 3)) ^ 2







noncomputable def cardyCrossing (s : ℝ) : ℝ :=
  cardyPrefactor * s ^ ((1 : ℝ) / 3) *
    ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3) (4 / 3) s


lemma cardyPrefactor_pos : 0 < cardyPrefactor := by
  unfold cardyPrefactor
  have h1 : (0 : ℝ) < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : (0 : ℝ) < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  apply div_pos
  · positivity
  · positivity



@[simp] lemma cardyCrossing_zero : cardyCrossing 0 = 0 := by
  unfold cardyCrossing
  rw [Real.zero_rpow (by norm_num : (1 : ℝ) / 3 ≠ 0)]
  ring














def IsSimplePhase (κ : ℝ) : Prop := 0 ≤ κ ∧ κ ≤ 4




def IsSelfTouchingPhase (κ : ℝ) : Prop := 4 < κ ∧ κ < 8



def IsSpaceFillingPhase (κ : ℝ) : Prop := 8 ≤ κ




lemma sle_phase_trichotomy {κ : ℝ} (hκ : 0 ≤ κ) :
    IsSimplePhase κ ∨ IsSelfTouchingPhase κ ∨ IsSpaceFillingPhase κ := by
  unfold IsSimplePhase IsSelfTouchingPhase IsSpaceFillingPhase
  rcases le_or_gt κ 4 with h | h
  · exact Or.inl ⟨hκ, h⟩
  · rcases lt_or_ge κ 8 with h' | h'
    · exact Or.inr (Or.inl ⟨h, h'⟩)
    · exact Or.inr (Or.inr h')


lemma not_simple_and_selfTouching {κ : ℝ}
    (h : IsSimplePhase κ) : ¬ IsSelfTouchingPhase κ := by
  rintro ⟨h₁, _⟩
  linarith [h.2]


lemma not_selfTouching_and_spaceFilling {κ : ℝ}
    (h : IsSelfTouchingPhase κ) : ¬ IsSpaceFillingPhase κ := by
  unfold IsSpaceFillingPhase
  linarith [h.2]











noncomputable def sleDimension (κ : ℝ) : ℝ := 1 + κ / 8

@[simp] lemma sleDimension_apply (κ : ℝ) : sleDimension κ = 1 + κ / 8 := rfl


@[simp] lemma sleDimension_zero : sleDimension 0 = 1 := by simp [sleDimension]


@[simp] lemma sleDimension_eight : sleDimension 8 = 2 := by norm_num [sleDimension]


lemma sleDimension_mem_Icc {κ : ℝ} (h0 : 0 ≤ κ) (h8 : κ ≤ 8) :
    sleDimension κ ∈ Set.Icc (1 : ℝ) 2 := by
  constructor <;> simp only [sleDimension] <;> linarith


lemma sleDimension_strictMono : StrictMono sleDimension := by
  intro a b hab
  simp only [sleDimension]
  linarith










def kappaPercolation : ℝ := 6


def kappaIsing : ℝ := 3


noncomputable def kappaFKIsing : ℝ := 16 / 3


noncomputable def centralCharge (κ : ℝ) : ℝ := (3 * κ - 8) * (6 - κ) / (2 * κ)



lemma kappaPercolation_selfTouching : IsSelfTouchingPhase kappaPercolation := by
  constructor <;> norm_num [kappaPercolation]


lemma kappaIsing_simple : IsSimplePhase kappaIsing := by
  constructor <;> norm_num [kappaIsing]


lemma kappaFKIsing_selfTouching : IsSelfTouchingPhase kappaFKIsing := by
  constructor <;> norm_num [kappaFKIsing]



@[simp] lemma centralCharge_percolation : centralCharge kappaPercolation = 0 := by
  norm_num [centralCharge, kappaPercolation]


@[simp] lemma centralCharge_ising : centralCharge kappaIsing = 1 / 2 := by
  norm_num [centralCharge, kappaIsing]
















def IsCLEParameter (κ : ℝ) : Prop := 8 / 3 < κ ∧ κ ≤ 8





lemma IsCLEParameter.pos {κ : ℝ} (h : IsCLEParameter κ) : 0 < κ := by
  have : (0:ℝ) < 8 / 3 := by norm_num
  exact lt_trans this h.1









structure IsCLE {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (loops : Ω → Set (Set ℂ)) (μ : MeasureTheory.Measure Ω) : Prop where
  
  param : IsCLEParameter κ
  

  measurable : ∀ S : Set ℂ, MeasurableSet {ω | S ∈ loops ω}
  

  isProbability : MeasureTheory.IsProbabilityMeasure μ


lemma IsCLE.kappa_pos {Ω : Type*} [MeasurableSpace Ω]
    {κ : ℝ} {loops : Ω → Set (Set ℂ)} {μ : MeasureTheory.Measure Ω}
    (h : IsCLE κ loops μ) : 0 < κ :=
  h.param.pos

end StatMech.SLE
