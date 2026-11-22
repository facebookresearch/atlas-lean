/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.Symmetrization
import MathlibExt.CategoryTheory.Monoidal.Mod.ExtensionOfScalars
import Mathlib.CategoryTheory.Monoidal.ExternalProduct.KanExtension

/-!
# The complete native sequential/symmetric balanced induction presentation

The original monoidal symmetrization, tensor algebra map to the sphere monoid
and its balanced extension of scalars are compared with the actual native
sequential/symmetric operator-index Kan adjunction.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison

attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided
  originalSymmetricSequenceSymmetric degreeInclusionMonoidal

local notation "N" => CategoryTheory.Sequence.Index
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The full left associativity composite retains every original ordered pair coefficient. -/
theorem Uμ_associativity_left_coefficient (X Y Z : SymmetricSequence.{u, v}) (a b c : N) :
    ((DayFunctor.η (U.obj X) (U.obj Y)).app (a, b) ▷ (U.obj Z).functor.obj c) ≫
      (DayFunctor.η (U.obj X ⊗ U.obj Y) (U.obj Z)).app (a ⊗ b, c) ≫
        ((Uμ X Y ▷ U.obj Z) ≫ Uμ (X ⊗ Y) Z ≫ U.map (α_ X Y Z).hom).natTrans.app
          ((a ⊗ b) ⊗ c) =
    (restrictionPairComponent X Y a b ▷ (U.obj Z).functor.obj c) ≫
      restrictionPairComponent (X ⊗ Y) Z (a ⊗ b) c ≫
        (U.map (α_ X Y Z).hom).natTrans.app ((a ⊗ b) ⊗ c) := by
  have hη : (DayFunctor.η (U.obj X ⊗ U.obj Y) (U.obj Z)).app (a ⊗ b, c) ≫
      (Uμ X Y ▷ U.obj Z).natTrans.app ((a ⊗ b) ⊗ c) =
    ((Uμ X Y).natTrans.app (a ⊗ b) ▷ (U.obj Z).functor.obj c) ≫
      (DayFunctor.η (U.obj (X ⊗ Y)) (U.obj Z)).app (a ⊗ b, c) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      N PointedCGWH.{u, v} (Uμ X Y) (U.obj Z) (a ⊗ b) c
  change ((DayFunctor.η (U.obj X) (U.obj Y)).app (a, b) ▷ (U.obj Z).functor.obj c) ≫
      (DayFunctor.η (U.obj X ⊗ U.obj Y) (U.obj Z)).app (a ⊗ b, c) ≫
        (Uμ X Y ▷ U.obj Z).natTrans.app ((a ⊗ b) ⊗ c) ≫
          (Uμ (X ⊗ Y) Z).natTrans.app ((a ⊗ b) ⊗ c) ≫
            (U.map (α_ X Y Z).hom).natTrans.app ((a ⊗ b) ⊗ c) = _
  rw [reassoc_of% hη]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, Uμ_pair]
  rw [Uμ_pair_assoc]

/-- The full right associativity composite retains the original inverse ordered associator action. -/
theorem Uμ_associativity_right_coefficient (X Y Z : SymmetricSequence.{u, v}) (a b c : N) :
    ((DayFunctor.η (U.obj X) (U.obj Y)).app (a, b) ▷ (U.obj Z).functor.obj c) ≫
      (DayFunctor.η (U.obj X ⊗ U.obj Y) (U.obj Z)).app (a ⊗ b, c) ≫
        ((α_ (U.obj X) (U.obj Y) (U.obj Z)).hom ≫
          (U.obj X ◁ Uμ Y Z) ≫ Uμ X (Y ⊗ Z)).natTrans.app ((a ⊗ b) ⊗ c) =
    (α_ ((U.obj X).functor.obj a) ((U.obj Y).functor.obj b)
      ((U.obj Z).functor.obj c)).hom ≫
      ((U.obj X).functor.obj a ◁ restrictionPairComponent Y Z b c) ≫
        restrictionPairComponent X (Y ⊗ Z) a (b ⊗ c) ≫
          (U.obj (X ⊗ (Y ⊗ Z))).functor.map (α_ a b c).inv := by
  let g : U.obj X ⊗ (U.obj Y ⊗ U.obj Z) ⟶ U.obj (X ⊗ (Y ⊗ Z)) :=
    (U.obj X ◁ Uμ Y Z) ≫ Uμ X (Y ⊗ Z)
  have hα : ((DayFunctor.η (U.obj X) (U.obj Y)).app (a, b) ▷ (U.obj Z).functor.obj c) ≫
      (DayFunctor.η (U.obj X ⊗ U.obj Y) (U.obj Z)).app (a ⊗ b, c) ≫
        (α_ (U.obj X) (U.obj Y) (U.obj Z)).hom.natTrans.app ((a ⊗ b) ⊗ c) =
    (α_ ((U.obj X).functor.obj a) ((U.obj Y).functor.obj b) ((U.obj Z).functor.obj c)).hom ≫
      ((U.obj X).functor.obj a ◁ (DayFunctor.η (U.obj Y) (U.obj Z)).app (b, c)) ≫
        (DayFunctor.η (U.obj X) (U.obj Y ⊗ U.obj Z)).app (a, b ⊗ c) ≫
          (U.obj X ⊗ (U.obj Y ⊗ U.obj Z)).functor.map (α_ a b c).inv :=
    LawfulDayConvolutionMonoidalCategoryStruct.associator_hom_unit_unit
      PointedCGWH.{u, v} (U.obj X) (U.obj Y) (U.obj Z) a b c
  have hn := g.natTrans.naturality (α_ a b c).inv
  have hη : (DayFunctor.η (U.obj X) (U.obj Y ⊗ U.obj Z)).app (a, b ⊗ c) ≫
      (U.obj X ◁ Uμ Y Z).natTrans.app (a ⊗ (b ⊗ c)) =
    ((U.obj X).functor.obj a ◁ (Uμ Y Z).natTrans.app (b ⊗ c)) ≫
      (DayFunctor.η (U.obj X) (U.obj (Y ⊗ Z))).app (a, b ⊗ c) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      PointedCGWH.{u, v} (U.obj X) (Uμ Y Z) a (b ⊗ c)
  change ((DayFunctor.η (U.obj X) (U.obj Y)).app (a, b) ▷ (U.obj Z).functor.obj c) ≫
      (DayFunctor.η (U.obj X ⊗ U.obj Y) (U.obj Z)).app (a ⊗ b, c) ≫
        (α_ (U.obj X) (U.obj Y) (U.obj Z)).hom.natTrans.app ((a ⊗ b) ⊗ c) ≫
          g.natTrans.app ((a ⊗ b) ⊗ c) = _
  rw [reassoc_of% hα, hn]
  dsimp only [g]
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% hη, ← MonoidalCategory.whiskerLeft_comp_assoc, Uμ_pair, Uμ_pair_assoc]

/-- Every actual restriction tensorator preserves the whole original associativity diagram. -/
theorem Uμ_associativity (X Y Z : SymmetricSequence.{u, v}) :
    Uμ X Y ▷ U.obj Z ≫ Uμ (X ⊗ Y) Z ≫ U.map (α_ X Y Z).hom =
      (α_ (U.obj X) (U.obj Y) (U.obj Z)).hom ≫ (U.obj X ◁ Uμ Y Z) ≫ Uμ X (Y ⊗ Z) := by
  apply DayFunctor.tensor_hom_ext
  intro a b
  let h :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      (C := N) (V := PointedCGWH.{u, v})
      (D := CategoryTheory.Sequence PointedCGWH.{u, v}) (U.obj X) (U.obj Y) a
  apply (isColimitOfPreserves (tensorRight ((U.obj Z).functor.obj b)) h).hom_ext
  intro d
  obtain ⟨pq, f, rfl⟩ := CostructuredArrow.mk_surjective d
  rcases pq with ⟨p, q⟩
  have ha : a = p ⊗ q := (Discrete.ext (Discrete.eq_of_hom f)).symm
  subst a
  have hf : f = 𝟙 (p ⊗ q) := Discrete.hom_eq
  cases hf
  change (((DayFunctor.η (U.obj X) (U.obj Y)).app (p, q) ≫
      (U.obj X ⊗ U.obj Y).functor.map (𝟙 (p ⊗ q))) ▷ (U.obj Z).functor.obj b) ≫
      (DayFunctor.η (U.obj X ⊗ U.obj Y) (U.obj Z)).app (p ⊗ q, b) ≫
        ((Uμ X Y ▷ U.obj Z) ≫ Uμ (X ⊗ Y) Z ≫ U.map (α_ X Y Z).hom).natTrans.app
          ((p ⊗ q) ⊗ b) =
    (((DayFunctor.η (U.obj X) (U.obj Y)).app (p, q) ≫
      (U.obj X ⊗ U.obj Y).functor.map (𝟙 (p ⊗ q))) ▷ (U.obj Z).functor.obj b) ≫
      (DayFunctor.η (U.obj X ⊗ U.obj Y) (U.obj Z)).app (p ⊗ q, b) ≫
        ((α_ (U.obj X) (U.obj Y) (U.obj Z)).hom ≫
          (U.obj X ◁ Uμ Y Z) ≫ Uμ X (Y ⊗ Z)).natTrans.app ((p ⊗ q) ⊗ b)
  have hmap : (U.obj X ⊗ U.obj Y).functor.map (𝟙 (p ⊗ q)) =
      𝟙 ((U.obj X ⊗ U.obj Y).functor.obj (p ⊗ q)) :=
    (U.obj X ⊗ U.obj Y).functor.map_id (p ⊗ q)
  have hleg : (((DayFunctor.η (U.obj X) (U.obj Y)).app (p, q) ≫
      (U.obj X ⊗ U.obj Y).functor.map (𝟙 (p ⊗ q))) ▷ (U.obj Z).functor.obj b) =
      ((DayFunctor.η (U.obj X) (U.obj Y)).app (p, q) ▷ (U.obj Z).functor.obj b) :=
    congrArg (fun g => g ▷ (U.obj Z).functor.obj b)
      ((congrArg (fun g => (DayFunctor.η (U.obj X) (U.obj Y)).app (p, q) ≫ g) hmap).trans
        (Category.comp_id _))
  have hc := (Uμ_associativity_left_coefficient X Y Z p q b).trans
    ((restrictionPair_associativity X Y Z p q b).trans
      (Uμ_associativity_right_coefficient X Y Z p q b).symm)
  exact (congrArg (fun g => g ≫
      (DayFunctor.η (U.obj X ⊗ U.obj Y) (U.obj Z)).app (p ⊗ q, b) ≫
        ((Uμ X Y ▷ U.obj Z) ≫ Uμ (X ⊗ Y) Z ≫ U.map (α_ X Y Z).hom).natTrans.app
          ((p ⊗ q) ⊗ b)) hleg).trans
    (hc.trans (congrArg (fun g => g ≫
      (DayFunctor.η (U.obj X ⊗ U.obj Y) (U.obj Z)).app (p ⊗ q, b) ≫
        ((α_ (U.obj X) (U.obj Y) (U.obj Z)).hom ≫
          (U.obj X ◁ Uμ Y Z) ≫ Uμ X (Y ⊗ Z)).natTrans.app ((p ⊗ q) ⊗ b)) hleg).symm)

/-- The complete left unit composite retains the original degree-zero coefficient map. -/
theorem Uμ_left_unit_coefficient (X : SymmetricSequence.{u, v}) (a : N) :
    (DayFunctor.ν N PointedCGWH.{u, v} ▷ (U.obj X).functor.obj a) ≫
      (DayFunctor.η (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})) (U.obj X)).app ((𝟙_ N), a) ≫
        ((Uε ▷ U.obj X) ≫ Uμ (𝟙_ SymmetricSequence.{u, v}) X ≫ U.map (λ_ X).hom).natTrans.app
          ((𝟙_ N) ⊗ a) =
    (restrictionUnitComponent ▷ (U.obj X).functor.obj a) ≫
      restrictionPairComponent (𝟙_ SymmetricSequence.{u, v}) X (𝟙_ N) a ≫
        (U.map (λ_ X).hom).natTrans.app ((𝟙_ N) ⊗ a) := by
  have hη :
      (DayFunctor.η (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})) (U.obj X)).app ((𝟙_ N), a) ≫
        (Uε ▷ U.obj X).natTrans.app ((𝟙_ N) ⊗ a) =
      (Uε.natTrans.app (𝟙_ N) ▷ (U.obj X).functor.obj a) ≫
        (DayFunctor.η (U.obj (𝟙_ SymmetricSequence.{u, v})) (U.obj X)).app ((𝟙_ N), a) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      N PointedCGWH.{u, v} Uε (U.obj X) (𝟙_ N) a
  change (DayFunctor.ν N PointedCGWH.{u, v} ▷ (U.obj X).functor.obj a) ≫
      (DayFunctor.η (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})) (U.obj X)).app ((𝟙_ N), a) ≫
        (Uε ▷ U.obj X).natTrans.app ((𝟙_ N) ⊗ a) ≫
          (Uμ (𝟙_ SymmetricSequence.{u, v}) X).natTrans.app ((𝟙_ N) ⊗ a) ≫
            (U.map (λ_ X).hom).natTrans.app ((𝟙_ N) ⊗ a) = _
  rw [reassoc_of% hη, ← MonoidalCategory.comp_whiskerRight_assoc, Uε_unit, Uμ_pair_assoc]

/-- The complete right unit composite retains the original degree-zero coefficient map. -/
theorem Uμ_right_unit_coefficient (X : SymmetricSequence.{u, v}) (a : N) :
    ((U.obj X).functor.obj a ◁ DayFunctor.ν N PointedCGWH.{u, v}) ≫
      (DayFunctor.η (U.obj X) (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).app (a, (𝟙_ N)) ≫
        ((U.obj X ◁ Uε) ≫ Uμ X (𝟙_ SymmetricSequence.{u, v}) ≫ U.map (ρ_ X).hom).natTrans.app
          (a ⊗ (𝟙_ N)) =
    ((U.obj X).functor.obj a ◁ restrictionUnitComponent) ≫
      restrictionPairComponent X (𝟙_ SymmetricSequence.{u, v}) a (𝟙_ N) ≫
        (U.map (ρ_ X).hom).natTrans.app (a ⊗ (𝟙_ N)) := by
  have hη :
      (DayFunctor.η (U.obj X) (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).app (a, (𝟙_ N)) ≫
        (U.obj X ◁ Uε).natTrans.app (a ⊗ (𝟙_ N)) =
      ((U.obj X).functor.obj a ◁ Uε.natTrans.app (𝟙_ N)) ≫
        (DayFunctor.η (U.obj X) (U.obj (𝟙_ SymmetricSequence.{u, v}))).app (a, (𝟙_ N)) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      PointedCGWH.{u, v} (U.obj X) Uε a (𝟙_ N)
  change ((U.obj X).functor.obj a ◁ DayFunctor.ν N PointedCGWH.{u, v}) ≫
      (DayFunctor.η (U.obj X) (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).app (a, (𝟙_ N)) ≫
        (U.obj X ◁ Uε).natTrans.app (a ⊗ (𝟙_ N)) ≫
          (Uμ X (𝟙_ SymmetricSequence.{u, v})).natTrans.app (a ⊗ (𝟙_ N)) ≫
            (U.map (ρ_ X).hom).natTrans.app (a ⊗ (𝟙_ N)) = _
  rw [reassoc_of% hη, ← MonoidalCategory.whiskerLeft_comp_assoc, Uε_unit, Uμ_pair_assoc]

/-- The original restriction tensorator preserves the complete left unit diagram. -/
theorem Uμ_left_unitality (X : SymmetricSequence.{u, v}) :
    (λ_ (U.obj X)).hom = (Uε ▷ U.obj X) ≫ Uμ (𝟙_ SymmetricSequence.{u, v}) X ≫ U.map (λ_ X).hom := by
  apply DayFunctor.tensor_hom_ext
  intro a b
  let h := LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionUnitUnit
    N PointedCGWH.{u, v} (CategoryTheory.Sequence PointedCGWH.{u, v}) a
  apply (isColimitOfPreserves (tensorRight ((U.obj X).functor.obj b)) h).hom_ext
  intro d
  obtain ⟨n, f, rfl⟩ := CostructuredArrow.mk_surjective d
  have ha : a = 𝟙_ N := (Discrete.ext (Discrete.eq_of_hom f)).symm
  subst a
  have hf : f = 𝟙 (𝟙_ N) := Discrete.hom_eq
  cases hf
  cases n
  change ((DayFunctor.ν N PointedCGWH.{u, v} ≫
      (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})).functor.map (𝟙 (𝟙_ N))) ▷
      (U.obj X).functor.obj b) ≫
      (DayFunctor.η (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})) (U.obj X)).app ((𝟙_ N), b) ≫
        (λ_ (U.obj X)).hom.natTrans.app ((𝟙_ N) ⊗ b) =
    ((DayFunctor.ν N PointedCGWH.{u, v} ≫
      (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})).functor.map (𝟙 (𝟙_ N))) ▷
      (U.obj X).functor.obj b) ≫
      (DayFunctor.η (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})) (U.obj X)).app ((𝟙_ N), b) ≫
        ((Uε ▷ U.obj X) ≫ Uμ (𝟙_ SymmetricSequence.{u, v}) X ≫ U.map (λ_ X).hom).natTrans.app
          ((𝟙_ N) ⊗ b)
  have hmap : (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})).functor.map (𝟙 (𝟙_ N)) =
      𝟙 ((𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})).functor.obj (𝟙_ N)) :=
    (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})).functor.map_id (𝟙_ N)
  have hleg : ((DayFunctor.ν N PointedCGWH.{u, v} ≫
      (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})).functor.map (𝟙 (𝟙_ N))) ▷
        (U.obj X).functor.obj b) = DayFunctor.ν N PointedCGWH.{u, v} ▷ (U.obj X).functor.obj b :=
    congrArg (fun g => g ▷ (U.obj X).functor.obj b)
      ((congrArg (fun g => DayFunctor.ν N PointedCGWH.{u, v} ≫ g) hmap).trans (Category.comp_id _))
  have h₀ : (DayFunctor.ν N PointedCGWH.{u, v} ▷ (U.obj X).functor.obj b) ≫
      (DayFunctor.η (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})) (U.obj X)).app ((𝟙_ N), b) ≫
        (λ_ (U.obj X)).hom.natTrans.app ((𝟙_ N) ⊗ b) =
    (λ_ ((U.obj X).functor.obj b)).hom ≫ (U.obj X).functor.map (λ_ b).inv :=
    LawfulDayConvolutionMonoidalCategoryStruct.leftUnitor_hom_unit_app PointedCGWH.{u, v} (U.obj X) b
  have hc := h₀.trans ((restrictionPair_left_unit X b).symm.trans (Uμ_left_unit_coefficient X b).symm)
  exact (congrArg (fun g => g ≫
      (DayFunctor.η (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})) (U.obj X)).app ((𝟙_ N), b) ≫
        (λ_ (U.obj X)).hom.natTrans.app ((𝟙_ N) ⊗ b)) hleg).trans
    (hc.trans (congrArg (fun g => g ≫
      (DayFunctor.η (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})) (U.obj X)).app ((𝟙_ N), b) ≫
        ((Uε ▷ U.obj X) ≫ Uμ (𝟙_ SymmetricSequence.{u, v}) X ≫ U.map (λ_ X).hom).natTrans.app
          ((𝟙_ N) ⊗ b)) hleg).symm)

/-- The original restriction tensorator preserves the complete right unit diagram. -/
theorem Uμ_right_unitality (X : SymmetricSequence.{u, v}) :
    (ρ_ (U.obj X)).hom = (U.obj X ◁ Uε) ≫ Uμ X (𝟙_ SymmetricSequence.{u, v}) ≫ U.map (ρ_ X).hom := by
  apply DayFunctor.tensor_hom_ext
  intro a b
  let h := LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionUnitUnit
    N PointedCGWH.{u, v} (CategoryTheory.Sequence PointedCGWH.{u, v}) b
  apply (isColimitOfPreserves (tensorLeft ((U.obj X).functor.obj a)) h).hom_ext
  intro d
  obtain ⟨n, f, rfl⟩ := CostructuredArrow.mk_surjective d
  have hb : b = 𝟙_ N := (Discrete.ext (Discrete.eq_of_hom f)).symm
  subst b
  have hf : f = 𝟙 (𝟙_ N) := Discrete.hom_eq
  cases hf
  cases n
  change ((U.obj X).functor.obj a ◁ (DayFunctor.ν N PointedCGWH.{u, v} ≫
      (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})).functor.map (𝟙 (𝟙_ N)))) ≫
      (DayFunctor.η (U.obj X) (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).app (a, (𝟙_ N)) ≫
        (ρ_ (U.obj X)).hom.natTrans.app (a ⊗ (𝟙_ N)) =
    ((U.obj X).functor.obj a ◁ (DayFunctor.ν N PointedCGWH.{u, v} ≫
      (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})).functor.map (𝟙 (𝟙_ N)))) ≫
      (DayFunctor.η (U.obj X) (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).app (a, (𝟙_ N)) ≫
        ((U.obj X ◁ Uε) ≫ Uμ X (𝟙_ SymmetricSequence.{u, v}) ≫ U.map (ρ_ X).hom).natTrans.app
          (a ⊗ (𝟙_ N))
  have hmap : (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})).functor.map (𝟙 (𝟙_ N)) =
      𝟙 ((𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})).functor.obj (𝟙_ N)) :=
    (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})).functor.map_id (𝟙_ N)
  have hleg : ((U.obj X).functor.obj a ◁ (DayFunctor.ν N PointedCGWH.{u, v} ≫
      (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})).functor.map (𝟙 (𝟙_ N)))) =
      ((U.obj X).functor.obj a ◁ DayFunctor.ν N PointedCGWH.{u, v}) :=
    congrArg (fun g => (U.obj X).functor.obj a ◁ g)
      ((congrArg (fun g => DayFunctor.ν N PointedCGWH.{u, v} ≫ g) hmap).trans (Category.comp_id _))
  have h₀ : ((U.obj X).functor.obj a ◁ DayFunctor.ν N PointedCGWH.{u, v}) ≫
      (DayFunctor.η (U.obj X) (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).app (a, (𝟙_ N)) ≫
        (ρ_ (U.obj X)).hom.natTrans.app (a ⊗ (𝟙_ N)) =
    (ρ_ ((U.obj X).functor.obj a)).hom ≫ (U.obj X).functor.map (ρ_ a).inv :=
    LawfulDayConvolutionMonoidalCategoryStruct.rightUnitor_hom_unit_app PointedCGWH.{u, v} (U.obj X) a
  have hc := h₀.trans ((restrictionPair_right_unit X a).symm.trans (Uμ_right_unit_coefficient X a).symm)
  exact (congrArg (fun g => g ≫
      (DayFunctor.η (U.obj X) (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).app (a, (𝟙_ N)) ≫
        (ρ_ (U.obj X)).hom.natTrans.app (a ⊗ (𝟙_ N))) hleg).trans
    (hc.trans (congrArg (fun g => g ≫
      (DayFunctor.η (U.obj X) (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).app (a, (𝟙_ N)) ≫
        ((U.obj X ◁ Uε) ≫ Uμ X (𝟙_ SymmetricSequence.{u, v}) ≫ U.map (ρ_ X).hom).natTrans.app
          (a ⊗ (𝟙_ N))) hleg).symm)

/-- The full original sequence restriction carries its derived native lax monoidal structure. -/
@[instance_reducible]
def restrictionLaxMonoidal : U.{u, v}.LaxMonoidal where
  ε := Uε
  «μ» := Uμ
  μ_natural_left := Uμ_natural_left
  μ_natural_right := fun {X Y} X' f => Uμ_natural_right X' (Y := X) (Z := Y) f
  associativity := Uμ_associativity
  left_unitality := Uμ_left_unitality
  right_unitality := Uμ_right_unitality

attribute [local instance] restrictionLaxMonoidal

/-- The actual original Kan left adjoint has the oplax maps induced by the full restriction tensorator. -/
@[instance_reducible]
def symmetrizationOplaxMonoidal : G.{u, v}.OplaxMonoidal :=
  sequenceAdjunction.{u, v}.leftAdjointOplaxMonoidal

attribute [local instance] symmetrizationOplaxMonoidal

/-- The original Kan unit and counit preserve those complete native monoidal maps. -/
theorem sequenceAdjunctionIsMonoidal : sequenceAdjunction.{u, v}.IsMonoidal := inferInstance

attribute [local instance] sequenceAdjunctionIsMonoidal

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
