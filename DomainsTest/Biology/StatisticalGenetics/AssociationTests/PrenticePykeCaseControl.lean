/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.StatisticalGenetics.AssociationTests.PrenticePykeCaseControl
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic.FinCases

open MeasureTheory
open scoped ENNReal

namespace PrenticePykeCaseControlTest

-- Four equally likely individuals: both cases and one of the two controls are sampled.
private noncomputable def μ : Measure (Fin 4) := (4 : ℝ≥0∞)⁻¹ • Measure.count

private def D : Set (Fin 4) := ({0, 1} : Finset (Fin 4))
private def S : Set (Fin 4) := ({0, 1, 2} : Finset (Fin 4))

example : μ.real D / μ.real Set.univ = 1 / 2 ∧
    μ.real (D ∩ S) / μ.real S = Real.sigmoid (Real.log 2) ∧
    Real.sigmoid (Real.log 2) = 2 / 3 := by
  have hmass (t : Finset (Fin 4)) : μ.real (t : Set (Fin 4)) = (t.card : ℝ) / 4 := by
    rw [μ, measureReal_ennreal_smul_apply, Measure.real, Measure.count_apply_finset]
    norm_num [div_eq_inv_mul]
  have huniv : μ.real (Set.univ : Set (Fin 4)) = 1 := by
    rw [← Finset.coe_univ, hmass, Finset.card_univ, Fintype.card_fin]
    norm_num
  let : IsProbabilityMeasure μ := isProbabilityMeasure_iff_real.mpr huniv
  have hD : μ.real D = 1 / 2 := by
    rw [D, hmass]
    norm_num
  have hS : μ.real S = 3 / 4 := by
    rw [S, hmass]
    norm_num
  have hDS : D ∩ S = D := by
    ext i
    fin_cases i <;> simp [D, S]
  have hSc : S ∩ Dᶜ = (↑({2} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext i
    fin_cases i <;> simp [D, S]
  have hDc : Dᶜ = (↑({2, 3} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext i
    fin_cases i <;> simp [D]
  have hshift : μ.real (D ∩ S) / μ.real S = Real.sigmoid (Real.log 2) := by
    let X : Fin 4 → Unit := fun _ ↦ ()
    have hX (x : Unit) : X ⁻¹' {x} = Set.univ := by cases x; simp [X]
    have h :=
      WantedExt.Biology.StatisticalGenetics.PrenticePykeCaseControlWanted.caseControl_logistic
        (K := 0) μ X measurable_const (fun _ ↦ 0) D S
        (D.toFinite.measurableSet) (S.toFinite.measurableSet) 0 0 (1 / 2) 1
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by intro x; simp only [hX, Set.inter_univ, dotProduct_zero, add_zero, Real.sigmoid_zero,
              huniv, mul_one, hD]; norm_num)
        (by intro x; simp only [hX, Set.inter_univ, Set.inter_comm S D, hDS, one_mul])
        (by intro x; rw [hX, Set.inter_univ, Set.inter_univ, hSc, hDc, hmass, hmass]; norm_num)
        () (by rw [hX, huniv]; norm_num)
    convert h using 2 <;> simp [hX]
  refine ⟨?_, hshift, ?_⟩
  · rw [huniv, div_one, hD]
  · rw [← hshift, hDS, hD, hS]
    norm_num

end PrenticePykeCaseControlTest
