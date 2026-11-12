/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































































import Code.Walls.rc17arbitrary
import Code.Walls.rc20reflection
import Code.Walls.rc83downstreamaudit

open MeasureTheory Finset
open scoped NNReal

namespace StatMech

open ConfigSpace
open StatMech.Walls








theorem rc84_target_is_genuine (h : ReimerWprobCore) {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_core h hp A B








theorem rc84_minimal_residue (h : rc17_NonMonotoneDeficit) : ReimerWprobCore :=
  rc17_reimerWprobCore_of_nonMonotone h




theorem rc84_reimer_of_minimal_residue (h : rc17_NonMonotoneDeficit)
    {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  rc17_reimer_inequality_of_nonMonotone h hp A B







theorem rc84_residue_is_famCylBox (h : rc20_FamCylBoxResidue) : ReimerWprobCore := by
  
  have h18 : rc18_CylBoxReflInter := (rc20_famCylBoxResidue_iff_cylBoxReflInter).mp h
  have h17 : rc17_NonMonotoneDeficit := (rc18_cylBoxReflInter_iff_nonMonotone).mp h18
  exact rc17_reimerWprobCore_of_nonMonotone h17










theorem rc84_what_is_proved :
    (∀ {n : ℕ} {A B : Set (ConfigSpace (Fin n))},
        (IsIncreasing A ∨ IsDecreasing A) → (IsIncreasing B ∨ IsDecreasing B) →
        rc5_deficit A B ≤ 0)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))),
        #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) :=
  ⟨fun hA hB => rc17_deficit_le_zero_of_bothMonotone hA hB,
   fun 𝒜 ℬ => rc20_famCylBox_fin2 𝒜 ℬ⟩








theorem rc84_off_critical_path {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0}
    (hp : p ≤ 1) {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  rc83_reimer_not_needed_for_increasing hp hA hB

















theorem rc84_target_status :
    
    (ReimerWprobCore →
      ∀ {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
        (A B : Set (ConfigSpace E)),
        (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
          ≤ (bernoulliProductMeasure (E := E) p hp).real A
            * (bernoulliProductMeasure (E := E) p hp).real B)
    
    ∧ (rc17_NonMonotoneDeficit → ReimerWprobCore)
    
    ∧ (∀ {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
        {A B : Set (ConfigSpace E)}, IsIncreasing A → IsIncreasing B →
        (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
          ≤ (bernoulliProductMeasure (E := E) p hp).real A
            * (bernoulliProductMeasure (E := E) p hp).real B)
    
    ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))),
        #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) :=
  ⟨fun h _ _ _ _ hp A B => rc84_target_is_genuine h hp A B,
   rc84_minimal_residue,
   fun {_ _ _} {_} hp {_ _} hA hB => rc84_off_critical_path hp hA hB,
   fun 𝒜 ℬ => rc20_famCylBox_fin2 𝒜 ℬ⟩

end StatMech
