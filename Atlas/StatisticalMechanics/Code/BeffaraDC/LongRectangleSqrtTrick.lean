/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















import Mathlib
import Code.Universality.RSWStrip

open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatMech

namespace BeffaraDC

open StatMech.Universality




theorem finite_complUnion_fkg_bound {ι E : Type*}
    (μ : Measure (ConfigSpace E)) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (s : Finset ι)
    (A : ι → Set (ConfigSpace E))
    (hA : ∀ i ∈ s, IsIncreasing (A i))
    (hAm : ∀ i ∈ s, MeasurableSet (A i)) :
    (∏ i ∈ s, (1 - μ.real (A i))) ≤
      1 - μ.real (⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [measureReal_def]
  | @insert i s hi ih =>
      have hAi : IsIncreasing (A i) := hA i (Finset.mem_insert_self i s)
      have hAim : MeasurableSet (A i) := hAm i (Finset.mem_insert_self i s)
      have hAs : ∀ j ∈ s, IsIncreasing (A j) := fun j hj =>
        hA j (Finset.mem_insert_of_mem hj)
      have hAsm : ∀ j ∈ s, MeasurableSet (A j) := fun j hj =>
        hAm j (Finset.mem_insert_of_mem hj)
      have hUnionInc : IsIncreasing (⋃ j ∈ s, A j) := by
        exact isUpperSet_iUnion₂ (fun j hj => hAs j hj)
      have hUnionMeas : MeasurableSet (⋃ j ∈ s, A j) :=
        Finset.measurableSet_biUnion s hAsm
      have hmiss_nonneg : 0 ≤ 1 - μ.real (A i) := by
        linarith [measureReal_le_one (μ := μ) (s := A i)]
      have hstep := complUnion_fkg_bound μ hpa hAi hUnionInc hAim hUnionMeas
      rw [Finset.prod_insert hi]
      calc
        (1 - μ.real (A i)) * ∏ j ∈ s, (1 - μ.real (A j))
            ≤ (1 - μ.real (A i)) * (1 - μ.real (⋃ j ∈ s, A j)) :=
          mul_le_mul_of_nonneg_left (ih hAs hAsm) hmiss_nonneg
        _ ≤ 1 - μ.real (A i ∪ ⋃ j ∈ s, A j) := hstep
        _ = 1 - μ.real (⋃ j ∈ insert i s, A j) := by
          congr 2
          ext ω
          simp





theorem finite_symmetric_sqrt_trick {ι E : Type*}
    (μ : Measure (ConfigSpace E)) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (s : Finset ι)
    (A : ι → Set (ConfigSpace E)) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hA : ∀ i ∈ s, IsIncreasing (A i))
    (hAm : ∀ i ∈ s, MeasurableSet (A i))
    (hsym : ∀ i ∈ s, μ.real (A i) = μ.real (A i₀)) :
    1 - (1 - μ.real (⋃ i ∈ s, A i)) ^ ((1 : ℝ) / s.card) ≤
      μ.real (A i₀) := by
  have hcardNat : 0 < s.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hcardNat
  have hmiss : 0 ≤ 1 - μ.real (A i₀) := by
    linarith [measureReal_le_one (μ := μ) (s := A i₀)]
  have hprod := finite_complUnion_fkg_bound μ hpa s A hA hAm
  have hpow : (1 - μ.real (A i₀)) ^ s.card ≤
      1 - μ.real (⋃ i ∈ s, A i) := by
    calc
      (1 - μ.real (A i₀)) ^ s.card =
          ∏ i ∈ s, (1 - μ.real (A i)) := by
        rw [← Finset.prod_const]
        apply Finset.prod_congr rfl
        intro i hi
        rw [hsym i hi]
      _ ≤ 1 - μ.real (⋃ i ∈ s, A i) := hprod
  have hrootExp : 0 ≤ (1 : ℝ) / s.card := (div_pos one_pos hcard).le
  have hmono :
      ((1 - μ.real (A i₀)) ^ s.card) ^ ((1 : ℝ) / s.card) ≤
        (1 - μ.real (⋃ i ∈ s, A i)) ^ ((1 : ℝ) / s.card) :=
    Real.rpow_le_rpow (pow_nonneg hmiss _) hpow hrootExp
  have hreduce :
      ((1 - μ.real (A i₀)) ^ s.card) ^ ((1 : ℝ) / s.card) =
        1 - μ.real (A i₀) := by
    rw [← Real.rpow_natCast (1 - μ.real (A i₀)) s.card,
      ← Real.rpow_mul hmiss]
    have hcard_ne : (s.card : ℝ) ≠ 0 := ne_of_gt hcard
    rw [show (s.card : ℝ) * (1 / (s.card : ℝ)) = 1 by field_simp]
    simp
  rw [hreduce] at hmono
  linarith




theorem finite_symmetric_deficit {ι E : Type*}
    (μ : Measure (ConfigSpace E)) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (s : Finset ι)
    (A : ι → Set (ConfigSpace E)) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hA : ∀ i ∈ s, IsIncreasing (A i))
    (hAm : ∀ i ∈ s, MeasurableSet (A i))
    (hsym : ∀ i ∈ s, μ.real (A i) = μ.real (A i₀))
    {δ : ℝ}
    (hunion : 1 - μ.real (⋃ i ∈ s, A i) ≤ δ) :
    1 - δ ^ ((1 : ℝ) / s.card) ≤ μ.real (A i₀) := by
  have hcardNat : 0 < s.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hcardNat
  have hUnionMiss : 0 ≤ 1 - μ.real (⋃ i ∈ s, A i) := by
    linarith [measureReal_le_one (μ := μ) (s := ⋃ i ∈ s, A i)]
  have hroot := Real.rpow_le_rpow hUnionMiss hunion (div_pos one_pos hcard).le
  have hsqrt := finite_symmetric_sqrt_trick μ hpa s A hi₀ hA hAm hsym
  linarith





theorem finite_symmetric_polynomial_deficit {ι E : Type*}
    (μ : Measure (ConfigSpace E)) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (s : Finset ι)
    (A : ι → Set (ConfigSpace E)) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hA : ∀ i ∈ s, IsIncreasing (A i))
    (hAm : ∀ i ∈ s, MeasurableSet (A i))
    (hsym : ∀ i ∈ s, μ.real (A i) = μ.real (A i₀))
    {c ε : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n)
    (hunion : 1 - μ.real (⋃ i ∈ s, A i) ≤ c * (n : ℝ) ^ (-ε)) :
    1 - c ^ ((1 : ℝ) / s.card) *
        (n : ℝ) ^ (-ε / s.card) ≤ μ.real (A i₀) := by
  have hcardNat : 0 < s.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hcardNat
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have halgebra :
      (c * (n : ℝ) ^ (-ε)) ^ ((1 : ℝ) / s.card) =
        c ^ ((1 : ℝ) / s.card) * (n : ℝ) ^ (-ε / s.card) := by
    rw [Real.mul_rpow hc (Real.rpow_nonneg hnpos.le _), ← Real.rpow_mul hnpos.le]
    congr 2
    ring
  have hroot := finite_symmetric_deficit μ hpa s A hi₀ hA hAm hsym hunion
  rwa [halgebra] at hroot

end BeffaraDC

end StatMech
