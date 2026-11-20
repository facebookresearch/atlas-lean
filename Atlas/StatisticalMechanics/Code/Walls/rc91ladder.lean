/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Code.Walls.rc86consolidation
import Code.Walls.rc90self

set_option linter.style.longLine false



set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset MeasureTheory
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace






open Classical in













theorem rc91_full_ladder :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ∅ B).card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        (rc80_disjOccG A (∅ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ∅).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a : ConfigSpace ι) (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG {a} B).card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (b : ConfigSpace ι),
        (rc80_disjOccG A ({b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A {b}).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B).card
          ≤ (rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B).card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (a b : ConfigSpace ι),
        (rc80_disjOccG A ({a, b} : Finset (ConfigSpace ι))).card
          ≤ (rc80_reflInterG A ({a, b} : Finset (ConfigSpace ι))).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B).card
          ≤ (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        (rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι))).card
          ≤ (rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι))).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        A ∩ B = ∅ → (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        (rc80_disjOccG A (rc89_setCompl A)).card ≤ (rc80_reflInterG A (rc89_setCompl A)).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc90_ReflCover A B → (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        rc90_ComplClosed A → (rc80_disjOccG A A).card ≤ (rc80_reflInterG A A).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc80_IsUpper A → rc80_IsLower B → rc80_disjOccG A B = A ∩ B) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc80_IsLower A → rc80_IsUpper B → rc80_disjOccG A B = A ∩ B) ∧
    
    (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)),
        (rc80_disjOccG A₁ B₁).card ≤ (rc80_reflInterG A₁ B₁).card →
        (rc80_disjOccG A₂ B₂).card ≤ (rc80_reflInterG A₂ B₂).card →
        (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
          ≤ (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) :=
  ⟨fun B => rc85_wall_empty_left B,
   fun A => rc85_wall_empty_right A,
   fun a B => rc85_wall_singleton_left a B,
   fun A b => rc85_wall_singleton_right A b,
   fun a b B => rc88_wall_twogen_left a b B,
   fun A a b => rc88_wall_twogen_right A a b,
   fun B => rc87_wall_univ_left B,
   fun A => rc87_wall_univ_right A,
   fun A B h => rc89_wall_disjoint A B h,
   fun A => rc89_wall_setcompl A,
   fun A B h => rc90_wall_reflCover A B h,
   fun A h => rc90_wall_self_complClosed A h,
   fun _ _ hA hB => rc80_disjOcc_eq_inter_of_upper_lower hA hB,
   fun _ _ hA hB => rc82_disjOccG_eq_inter_of_lower_upper hA hB,
   fun A₁ B₁ A₂ B₂ => rc80_wall_product A₁ B₁ A₂ B₂,
   rc79_top_wall_fin2⟩



open Classical in








theorem rc91_chain :
    (rc64_ReimerLeaf → rc60_BoxUnionBound) ∧
    (rc60_BoxUnionBound → ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))),
        #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧
    (rc60_BoxUnionBound → ReimerWprobCore) ∧
    (rc20_FamCylBoxResidue → ReimerWprobCore) ∧
    (∀ (_h : ReimerWprobCore) {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
        (A B : Set (ConfigSpace E)),
        (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
          ≤ (bernoulliProductMeasure (E := E) p hp).real A
            * (bernoulliProductMeasure (E := E) p hp).real B) :=
  rc86_complete_chain



open Classical in











theorem rc91_minimal_residue :
    (rc20_FamCylBoxResidue → ReimerWprobCore) ∧
    (rc17_NonMonotoneDeficit → ReimerWprobCore) ∧
    (rc64_ReimerLeaf → ReimerWprobCore) :=
  rc86_minimal_residue



open Classical in



















theorem rc91_status :
    
    (rc64_ReimerLeaf → rc60_BoxUnionBound) ∧
    (rc60_BoxUnionBound → ReimerWprobCore) ∧
    (rc60_BoxUnionBound → ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))),
        #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧
    (∀ (_h : ReimerWprobCore) {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
        (A B : Set (ConfigSpace E)),
        (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
          ≤ (bernoulliProductMeasure (E := E) p hp).real A
            * (bernoulliProductMeasure (E := E) p hp).real B) ∧
    
    (rc20_FamCylBoxResidue → ReimerWprobCore) ∧
    
    ((∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ∅ B).card) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        (rc80_disjOccG A (∅ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ∅).card) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a : ConfigSpace ι) (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG {a} B).card) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (b : ConfigSpace ι),
        (rc80_disjOccG A ({b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A {b}).card) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B).card
          ≤ (rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B).card) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (a b : ConfigSpace ι),
        (rc80_disjOccG A ({a, b} : Finset (ConfigSpace ι))).card
          ≤ (rc80_reflInterG A ({a, b} : Finset (ConfigSpace ι))).card) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B).card
          ≤ (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        (rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι))).card
          ≤ (rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι))).card) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        A ∩ B = ∅ → (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        (rc80_disjOccG A (rc89_setCompl A)).card ≤ (rc80_reflInterG A (rc89_setCompl A)).card) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc90_ReflCover A B → (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        rc90_ComplClosed A → (rc80_disjOccG A A).card ≤ (rc80_reflInterG A A).card) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc80_IsUpper A → rc80_IsLower B → rc80_disjOccG A B = A ∩ B) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc80_IsLower A → rc80_IsUpper B → rc80_disjOccG A B = A ∩ B) ∧
      (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)),
        (rc80_disjOccG A₁ B₁).card ≤ (rc80_reflInterG A₁ B₁).card →
        (rc80_disjOccG A₂ B₂).card ≤ (rc80_reflInterG A₂ B₂).card →
        (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
          ≤ (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card) ∧
      (∀ A B : Finset (ConfigSpace (Fin 2)),
        (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card)) ∧
    
    (∀ {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
        {A B : Set (ConfigSpace E)}, IsIncreasing A → IsIncreasing B →
        (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
          ≤ (bernoulliProductMeasure (E := E) p hp).real A
            * (bernoulliProductMeasure (E := E) p hp).real B) :=
  ⟨rc64_boxUnionBound_of_leaf,
   rc64_reimerWprobCore_of_boxUnionBound,
   fun h m 𝒜 ℬ => rc64_wall_of_boxUnionBound h m 𝒜 ℬ,
   fun h _ _ _ _ hp A B => reimer_inequality_of_core h hp A B,
   StatMech.rc84_residue_is_famCylBox,
   rc91_full_ladder,
   fun {_ _ _} {_} hp {_ _} hA hB => StatMech.rc84_off_critical_path hp hA hB⟩

end StatMech.Walls
