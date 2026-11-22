/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionMonoidal
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.ModuleData
import MathlibExt.CategoryTheory.Monoidal.Mod.MonoidalAdjunction
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.OrderedTensorAlgebra
import MathlibExt.CategoryTheory.Functor.KanExtension.CompositeUnit
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.Extensionality
import MathlibExt.CategoryTheory.Monoidal.Mod.ScalarRestriction
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.DayFunctorClosedSymmetric
import MathlibExt.Topology.Category.PointedCGWH.EnrichedMappingEnds

/-!
# The complete original sequential/symmetric induction comparison

The original free symmetrization and balanced tensor along the actual tensor
algebra map to the sphere monoid are compared with the full native Kan pair.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison

attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided
  originalSymmetricSequenceSymmetric degreeInclusionMonoidal
  restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal

local notation "N" => CategoryTheory.Sequence.Index
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

export CategoryTheory.Functor.KanExtension
  (externalCompositeIndexIso externalCompositeUnit externalCompositeUnit_app externalCompositeUnit_isLeftKan)

export CategoryTheory.Functor.KanExtension
  (kanCompositeUnit kanCompositeUnit_app kanCompositeUnit_isLeftKan)

alias lawfulDay_unit_hom_ext := CategoryTheory.LawfulDayConvolutionMonoidalCategoryStruct.unit_hom_ext
alias lawfulDay_tensor_hom_ext := CategoryTheory.LawfulDayConvolutionMonoidalCategoryStruct.tensor_hom_ext


/-- The original restriction tensorator carries every full Day action coefficient before any monoid is selected. -/
theorem restrictionPair_action (X Y Z : SymmetricSequence.{u, v})
    (s : X ⊗ Y ⟶ Z) (a b : N) :
    (DayFunctor.η (U.obj X) (U.obj Y)).app (a, b) ≫
      (Uμ X Y ≫ U.map s).natTrans.app (a ⊗ b) =
    (DayFunctor.η X Y).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
      s.natTrans.app (degreeInclusion.obj (a ⊗ b)) := by
  have hcomp : (Uμ X Y ≫ U.map s).natTrans.app (a ⊗ b) =
      (Uμ X Y).natTrans.app (a ⊗ b) ≫ (U.map s).natTrans.app (a ⊗ b) := rfl
  exact (congrArg (fun q => (DayFunctor.η (U.obj X) (U.obj Y)).app (a, b) ≫ q) hcomp).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ (U.map s).natTrans.app (a ⊗ b)) (Uμ_pair X Y a b)).trans
        ((congrArg (fun q => q ≫ (U.map s).natTrans.app (a ⊗ b))
          (restrictionPairComponent_eq X Y a b)).trans
            (congrArg (fun q =>
              (DayFunctor.η X Y).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫ q)
              (U_map_component s (a ⊗ b))))))

/-- An arbitrary original scalar map and full action retain the complete ordered restriction pair formula. -/
theorem restrictionScalarPair_action (A : CategoryTheory.Sequence PointedCGWH.{u, v})
    (X Y Z : SymmetricSequence.{u, v}) (i : A ⟶ U.obj X) (s : X ⊗ Y ⟶ Z) (a b : N) :
    (DayFunctor.η A (U.obj Y)).app (a, b) ≫
      ((i ▷ U.obj Y) ≫ Uμ X Y ≫ U.map s).natTrans.app (a ⊗ b) =
    (i.natTrans.app a ⊗ₘ 𝟙 ((U.obj Y).functor.obj b)) ≫
      (DayFunctor.η X Y).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
        s.natTrans.app (degreeInclusion.obj (a ⊗ b)) := by
  have h := day_scalar_action_pair i (Uμ X Y ≫ U.map s) a b
  exact h.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => (i.natTrans.app a ⊗ₘ 𝟙 ((U.obj Y).functor.obj b)) ≫ q)
      (restrictionPair_action X Y Z s a b)).trans (Category.assoc _ _ _)))


alias monoidalScalarRestriction := CategoryTheory.Mod.MonoidalAdjunction.scalarRestriction
alias monoidalScalarRestriction_action := CategoryTheory.Mod.MonoidalAdjunction.scalarRestriction_action

/-- The actual original Kan unit before the Day wrapper is applied. -/
def GUnit (X : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    X.functor ⟶ degreeInclusion ⋙ (G.obj X).functor :=
  degreeInclusion.leftKanExtensionUnit X.functor

/-- The complete original pair unit for symmetrization. -/
def GExternalUnit (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    X.functor ⊠ Y.functor ⟶ degreeInclusion.prod degreeInclusion ⋙
      (G.obj X).functor ⊠ (G.obj Y).functor where
  app q := (GUnit X).app q.1 ⊗ₘ (GUnit Y).app q.2
  naturality := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ f
    have ha : a = a' := Discrete.ext (Discrete.eq_of_hom f.1)
    have hb : b = b' := Discrete.ext (Discrete.eq_of_hom f.2)
    subst a'
    subst b'
    have hf : f = 𝟙 (a, b) := by ext <;> exact Discrete.hom_eq
    cases hf
    exact (congrArg (fun g => g ≫ ((GUnit X).app a ⊗ₘ (GUnit Y).app b))
      ((X.functor ⊠ Y.functor).map_id (a, b))).trans
        ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          (congrArg (fun g => ((GUnit X).app a ⊗ₘ (GUnit Y).app b) ≫ g)
            ((degreeInclusion.prod degreeInclusion ⋙
              (G.obj X).functor ⊠ (G.obj Y).functor).map_id (a, b)).symm)))

/-- The original ordered tensor comparison retains the same full finite-block maps. -/
def tensorIndexIso : tensor N ⋙ degreeInclusion ≅
    degreeInclusion.prod degreeInclusion ⋙ tensor I :=
  NatIso.ofComponents (fun q => (degreeTensorIso q.1 q.2).symm) (by
    rintro ⟨a, b⟩ ⟨a', b'⟩ f
    have ha : a = a' := Discrete.ext (Discrete.eq_of_hom f.1)
    have hb : b = b' := Discrete.ext (Discrete.eq_of_hom f.2)
    subst a'
    subst b'
    have hf : f = 𝟙 (a, b) := by ext <;> exact Discrete.hom_eq
    cases hf
    exact (congrArg (fun g => g ≫ (degreeTensorIso a b).inv)
      ((tensor N ⋙ degreeInclusion).map_id (a, b))).trans
        ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          (congrArg (fun g => (degreeTensorIso a b).inv ≫ g)
            ((degreeInclusion.prod degreeInclusion ⋙ tensor I).map_id (a, b)).symm))))

/-- The original symmetrization unit is a genuine pointwise left Kan extension on the full native diagram. -/
def GPointwise (X : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    (Functor.LeftExtension.mk (G.obj X).functor (GUnit X)).IsPointwiseLeftKanExtension :=
  degreeInclusion.isPointwiseLeftKanExtensionLeftKanExtensionUnit X.functor

/-- The first actual external-product Kan extension keeps the original left coefficient unit. -/
def GExternalLeftPointwise (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    (Functor.LeftExtension.mk ((G.obj X).functor ⊠ Y.functor)
      (ExternalProduct.extensionUnitLeft (G.obj X).functor (GUnit X) Y.functor)).IsPointwiseLeftKanExtension :=
  ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitLeft (G.obj X).functor
    (GUnit X) Y.functor (GPointwise X)

/-- The second actual external-product Kan extension keeps the original right coefficient unit. -/
def GExternalRightPointwise (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    (Functor.LeftExtension.mk ((G.obj X).functor ⊠ (G.obj Y).functor)
      (ExternalProduct.extensionUnitRight (G.obj Y).functor (GUnit Y)
        (G.obj X).functor)).IsPointwiseLeftKanExtension :=
  ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitRight (G.obj Y).functor
    (GUnit Y) (G.obj X).functor (GPointwise Y)

/-- The complete pasted unit is the original coefficientwise symmetrization unit. -/
theorem GExternalUnit_eq (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    externalCompositeUnit degreeInclusion (G.obj X).functor (G.obj Y).functor
      (GUnit X) (GUnit Y) = GExternalUnit X Y := by
  apply NatTrans.ext
  funext q
  exact externalCompositeUnit_app degreeInclusion (G.obj X).functor (G.obj Y).functor
    (GUnit X) (GUnit Y) q

/-- The entire external-product diagram is the genuine composite of the two original Kan extensions. -/
theorem GExternalIsLeftKan (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    ((G.obj X).functor ⊠ (G.obj Y).functor).IsLeftKanExtension (GExternalUnit X Y) := by
  let : ((G.obj X).functor ⊠ Y.functor).IsLeftKanExtension
      (ExternalProduct.extensionUnitLeft (G.obj X).functor (GUnit X) Y.functor) :=
    (GExternalLeftPointwise X Y).isLeftKanExtension
  let : ((G.obj X).functor ⊠ (G.obj Y).functor).IsLeftKanExtension
      (ExternalProduct.extensionUnitRight (G.obj Y).functor (GUnit Y) (G.obj X).functor) :=
    (GExternalRightPointwise X Y).isLeftKanExtension
  rw [← GExternalUnit_eq X Y]
  exact externalCompositeUnit_isLeftKan degreeInclusion (G.obj X).functor (G.obj Y).functor
    (GUnit X) (GUnit Y)

/-- The actual source tensor is extended first by ordered Day convolution and then by symmetrization. -/
def GSourceTensorUnit (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    X.functor ⊠ Y.functor ⟶ (tensor N ⋙ degreeInclusion) ⋙ (G.obj (X ⊗ Y)).functor :=
  kanCompositeUnit (tensor N) degreeInclusion (tensor N ⋙ degreeInclusion) (Iso.refl _)
    (G.obj (X ⊗ Y)).functor (DayFunctor.η X Y) (GUnit (X ⊗ Y))

/-- Every original source tensor generator retains the full ordered Day and Kan units. -/
theorem GSourceTensorUnit_app (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) (a b : N) :
    (GSourceTensorUnit X Y).app (a, b) =
      (DayFunctor.η X Y).app (a, b) ≫ (GUnit (X ⊗ Y)).app (a ⊗ b) := by
  rw [GSourceTensorUnit, kanCompositeUnit_app]
  simp only [Iso.refl_hom, NatTrans.id_app]
  have hm := (G.obj (X ⊗ Y)).functor.map_id ((tensor N ⋙ degreeInclusion).obj (a, b))
  exact (congrArg (fun g => (DayFunctor.η X Y).app (a, b) ≫
      (GUnit (X ⊗ Y)).app ((tensor N).obj (a, b)) ≫ g) hm).trans
    (congrArg (fun g => (DayFunctor.η X Y).app (a, b) ≫ g)
      (Category.comp_id ((GUnit (X ⊗ Y)).app ((tensor N).obj (a, b)))))

/-- The complete original source tensor is a genuine Kan extension along the original tensor inclusion. -/
theorem GSourceTensorIsLeftKan (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    (G.obj (X ⊗ Y)).functor.IsLeftKanExtension (GSourceTensorUnit X Y) := by
  let : (G.obj (X ⊗ Y)).functor.IsLeftKanExtension (GUnit (X ⊗ Y)) :=
    (GPointwise (X ⊗ Y)).isLeftKanExtension
  exact kanCompositeUnit_isLeftKan (tensor N) degreeInclusion (tensor N ⋙ degreeInclusion)
    (Iso.refl _) (G.obj (X ⊗ Y)).functor (DayFunctor.η X Y) (GUnit (X ⊗ Y))

/-- The actual target tensor extends both coefficients and then applies the original symmetric Day convolution. -/
def GTargetTensorUnit (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    X.functor ⊠ Y.functor ⟶ (tensor N ⋙ degreeInclusion) ⋙ (G.obj X ⊗ G.obj Y).functor :=
  kanCompositeUnit (degreeInclusion.prod degreeInclusion) (tensor I) (tensor N ⋙ degreeInclusion)
    tensorIndexIso.symm (G.obj X ⊗ G.obj Y).functor (GExternalUnit X Y)
      (DayFunctor.η (G.obj X) (G.obj Y))

/-- Every target generator retains both original coefficients and the complete ordered index map. -/
theorem GTargetTensorUnit_app (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) (a b : N) :
    (GTargetTensorUnit X Y).app (a, b) =
      ((GUnit X).app a ⊗ₘ (GUnit Y).app b) ≫
        (DayFunctor.η (G.obj X) (G.obj Y)).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
          (G.obj X ⊗ G.obj Y).functor.map (degreeTensorIso a b).hom := by
  exact kanCompositeUnit_app (degreeInclusion.prod degreeInclusion) (tensor I)
    (tensor N ⋙ degreeInclusion) tensorIndexIso.symm (G.obj X ⊗ G.obj Y).functor
      (GExternalUnit X Y) (DayFunctor.η (G.obj X) (G.obj Y)) (a, b)

/-- The complete original target tensor is the second genuine Kan extension along the same tensor inclusion. -/
theorem GTargetTensorIsLeftKan (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    (G.obj X ⊗ G.obj Y).functor.IsLeftKanExtension (GTargetTensorUnit X Y) := by
  let : ((G.obj X).functor ⊠ (G.obj Y).functor).IsLeftKanExtension (GExternalUnit X Y) :=
    GExternalIsLeftKan X Y
  exact kanCompositeUnit_isLeftKan (degreeInclusion.prod degreeInclusion) (tensor I)
    (tensor N ⋙ degreeInclusion) tensorIndexIso.symm (G.obj X ⊗ G.obj Y).functor
      (GExternalUnit X Y) (DayFunctor.η (G.obj X) (G.obj Y))

/-- The full monoidal-adjunction unit is the same original ordinary Kan unit on every diagram. -/
theorem GUnit_original (X : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    (sequenceAdjunction.unit.app X).natTrans = GUnit X := by
  apply NatTrans.ext
  funext a
  rw [sequenceAdjunction, Adjunction.comp_unit_app, Adjunction.comp_unit_app,
    Functor.lanAdjunction_unit]
  change 𝟙 (X.functor.obj a) ≫ (GUnit X).app a ≫
      𝟙 ((G.obj X).functor.obj (degreeInclusion.obj a)) = (GUnit X).app a
  simp only [Category.id_comp]
  exact Category.comp_id ((GUnit X).app a)

/-- The actual oplax tensor map preserves every original ordered Day and Kan generator. -/
theorem Gδ_pair (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) (a b : N) :
    (DayFunctor.η X Y).app (a, b) ≫ (GUnit (X ⊗ Y)).app (a ⊗ b) ≫
      (Functor.OplaxMonoidal.δ G X Y).natTrans.app (degreeInclusion.obj (a ⊗ b)) =
    ((GUnit X).app a ⊗ₘ (GUnit Y).app b) ≫
      restrictionPairComponent (G.obj X) (G.obj Y) a b := by
  have hu : (sequenceAdjunction.unit.app (X ⊗ Y)).natTrans.app (a ⊗ b) ≫
      (Functor.OplaxMonoidal.δ G X Y).natTrans.app (degreeInclusion.obj (a ⊗ b)) =
    (sequenceAdjunction.unit.app X ⊗ₘ sequenceAdjunction.unit.app Y).natTrans.app (a ⊗ b) ≫
      (Uμ (G.obj X) (G.obj Y)).natTrans.app (a ⊗ b) :=
    congrArg (fun f => f.natTrans.app (a ⊗ b))
      (sequenceAdjunction.unit_app_tensor_comp_map_δ X Y)
  have hη : (DayFunctor.η X Y).app (a, b) ≫
      (sequenceAdjunction.unit.app X ⊗ₘ sequenceAdjunction.unit.app Y).natTrans.app (a ⊗ b) =
    ((sequenceAdjunction.unit.app X).natTrans.app a ⊗ₘ
      (sequenceAdjunction.unit.app Y).natTrans.app b) ≫
        (DayFunctor.η (U.obj (G.obj X)) (U.obj (G.obj Y))).app (a, b) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_tensorHom_app
      N PointedCGWH.{u, v} (sequenceAdjunction.unit.app X) (sequenceAdjunction.unit.app Y) a b
  rw [GUnit_original] at hu
  rw [GUnit_original, GUnit_original] at hη
  calc
    _ = (DayFunctor.η X Y).app (a, b) ≫
        (sequenceAdjunction.unit.app X ⊗ₘ sequenceAdjunction.unit.app Y).natTrans.app (a ⊗ b) ≫
          (Uμ (G.obj X) (G.obj Y)).natTrans.app (a ⊗ b) :=
      congrArg (fun f => (DayFunctor.η X Y).app (a, b) ≫ f) hu
    _ = ((GUnit X).app a ⊗ₘ (GUnit Y).app b) ≫
        (DayFunctor.η (U.obj (G.obj X)) (U.obj (G.obj Y))).app (a, b) ≫
          (Uμ (G.obj X) (G.obj Y)).natTrans.app (a ⊗ b) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ (Uμ (G.obj X) (G.obj Y)).natTrans.app (a ⊗ b)) hη).trans
          (Category.assoc _ _ _))
    _ = _ := congrArg (fun f => ((GUnit X).app a ⊗ₘ (GUnit Y).app b) ≫ f)
      (Uμ_pair (G.obj X) (G.obj Y) a b)

/-- The actual original oplax tensor map is the full Kan comparison transformation. -/
theorem Gδ_fac (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    GSourceTensorUnit X Y ≫ whiskerLeft (tensor N ⋙ degreeInclusion)
      (Functor.OplaxMonoidal.δ G X Y).natTrans = GTargetTensorUnit X Y := by
  apply NatTrans.ext
  funext q
  rcases q with ⟨a, b⟩
  simp only [NatTrans.comp_app, whiskerLeft_app]
  rw [GSourceTensorUnit_app, GTargetTensorUnit_app]
  exact (Category.assoc _ _ _).trans (Gδ_pair X Y a b)

/-- The complete original tensor comparison is invertible on the full native symmetric diagram. -/
theorem Gδ_natTrans_isIso (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    IsIso (Functor.OplaxMonoidal.δ G X Y).natTrans := by
  let : (G.obj (X ⊗ Y)).functor.IsLeftKanExtension (GSourceTensorUnit X Y) :=
    GSourceTensorIsLeftKan X Y
  exact (Functor.isLeftKanExtension_iff_isIso (Functor.OplaxMonoidal.δ G X Y).natTrans
    (GSourceTensorUnit X Y) (GTargetTensorUnit X Y) (Gδ_fac X Y)).1
      (GTargetTensorIsLeftKan X Y)

/-- The actual original symmetrization tensor map is an isomorphism of Day functors. -/
theorem Gδ_isIso (X Y : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    IsIso (Functor.OplaxMonoidal.δ G X Y) := by
  let : IsIso ((DayFunctor.equiv I PointedCGWH.{u, v}).functor.map
      (Functor.OplaxMonoidal.δ G X Y)) := by
    change IsIso (Functor.OplaxMonoidal.δ G X Y).natTrans
    exact Gδ_natTrans_isIso X Y
  exact isIso_of_reflects_iso (Functor.OplaxMonoidal.δ G X Y)
    (DayFunctor.equiv I PointedCGWH.{u, v}).functor

/-- The original ordered unit inclusion retains its complete degree-zero index isomorphism. -/
def unitIndexIso : Functor.fromPUnit.{0} (𝟙_ N) ⋙ degreeInclusion ≅
    Functor.fromPUnit.{0} (𝟙_ I) :=
  NatIso.ofComponents (fun _ => degreeUnitIso.symm) (by
    intro a b f
    have h : a = b := Subsingleton.elim _ _
    subst b
    have hf : f = 𝟙 a := Subsingleton.elim _ _
    cases hf
    exact (congrArg (fun g => g ≫ degreeUnitIso.inv)
      ((Functor.fromPUnit.{0} (𝟙_ N) ⋙ degreeInclusion).map_id a)).trans
        ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          (congrArg (fun g => degreeUnitIso.inv ≫ g)
            ((Functor.fromPUnit.{0} (𝟙_ I)).map_id a).symm))))

/-- The original source Day unit is extended by the same actual symmetrization Kan unit. -/
def GSourceUnit : Functor.fromPUnit.{0} (𝟙_ PointedCGWH.{u, v}) ⟶
    Functor.fromPUnit.{0} (𝟙_ I) ⋙
      (G.obj (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).functor :=
  kanCompositeUnit (Functor.fromPUnit.{0} (𝟙_ N)) degreeInclusion
    (Functor.fromPUnit.{0} (𝟙_ I)) unitIndexIso
      (G.obj (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).functor
        (DayFunctor.νNatTrans N PointedCGWH.{u, v})
          (GUnit (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})))

/-- The complete source unit coefficient retains the original ordered degree-zero inverse map. -/
theorem GSourceUnit_app (q : Discrete PUnit.{1}) :
    GSourceUnit.{u, v}.app q = DayFunctor.ν N PointedCGWH.{u, v} ≫
      (GUnit (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).app (𝟙_ N) ≫
        (G.obj (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).functor.map degreeUnitIso.inv :=
  kanCompositeUnit_app (Functor.fromPUnit.{0} (𝟙_ N)) degreeInclusion
    (Functor.fromPUnit.{0} (𝟙_ I)) unitIndexIso
      (G.obj (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).functor
        (DayFunctor.νNatTrans N PointedCGWH.{u, v})
          (GUnit (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))) q

/-- The original symmetrized source unit is a genuine Kan extension along the original unit inclusion. -/
theorem GSourceUnitIsLeftKan :
    (G.obj (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).functor.IsLeftKanExtension
      GSourceUnit.{u, v} := by
  let : (G.obj (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).functor.IsLeftKanExtension
      (GUnit (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))) :=
    (GPointwise (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).isLeftKanExtension
  exact kanCompositeUnit_isLeftKan (Functor.fromPUnit.{0} (𝟙_ N)) degreeInclusion
    (Functor.fromPUnit.{0} (𝟙_ I)) unitIndexIso
      (G.obj (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).functor
        (DayFunctor.νNatTrans N PointedCGWH.{u, v})
          (GUnit (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v})))

/-- The actual oplax unit preserves the complete original degree-zero coefficient insertion. -/
@[reassoc]
theorem Gη_coefficient : DayFunctor.ν N PointedCGWH.{u, v} ≫
    (GUnit (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).app (𝟙_ N) ≫
      (Functor.OplaxMonoidal.η G.{u, v}).natTrans.app (degreeInclusion.obj (𝟙_ N)) =
    restrictionUnitComponent.{u, v} := by
  have hu : (sequenceAdjunction.unit.app (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).natTrans.app
      (𝟙_ N) ≫ (Functor.OplaxMonoidal.η G.{u, v}).natTrans.app (degreeInclusion.obj (𝟙_ N)) =
    Uε.{u, v}.natTrans.app (𝟙_ N) :=
    congrArg (fun f => f.natTrans.app (𝟙_ N))
      sequenceAdjunction.{u, v}.unit_app_unit_comp_map_η
  rw [GUnit_original] at hu
  exact (congrArg (fun f => DayFunctor.ν N PointedCGWH.{u, v} ≫ f) hu).trans Uε_unit.{u, v}

/-- The actual original oplax unit is the whole Kan comparison transformation for the Day unit. -/
theorem Gη_fac : GSourceUnit.{u, v} ≫ whiskerLeft (Functor.fromPUnit.{0} (𝟙_ I))
    (Functor.OplaxMonoidal.η G.{u, v}).natTrans = DayFunctor.νNatTrans I PointedCGWH.{u, v} := by
  apply NatTrans.ext
  funext q
  simp only [NatTrans.comp_app, whiskerLeft_app]
  rw [GSourceUnit_app]
  simp only [Category.assoc]
  change DayFunctor.ν N PointedCGWH.{u, v} ≫
      (GUnit (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).app (𝟙_ N) ≫
        (G.obj (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).functor.map degreeUnitIso.inv ≫
          (Functor.OplaxMonoidal.η G.{u, v}).natTrans.app (𝟙_ I) =
    DayFunctor.ν I PointedCGWH.{u, v}
  have hn := (Functor.OplaxMonoidal.η G.{u, v}).natTrans.naturality degreeUnitIso.inv
  rw [hn, Gη_coefficient_assoc]
  have hi : (𝟙_ SymmetricSequence.{u, v}).functor.map degreeUnitIso.hom ≫
      (𝟙_ SymmetricSequence.{u, v}).functor.map degreeUnitIso.inv =
    𝟙 ((𝟙_ SymmetricSequence.{u, v}).functor.obj (𝟙_ I)) :=
    ((𝟙_ SymmetricSequence.{u, v}).functor.mapIso degreeUnitIso).hom_inv_id
  change (DayFunctor.ν I PointedCGWH.{u, v} ≫
      (𝟙_ SymmetricSequence.{u, v}).functor.map degreeUnitIso.hom) ≫
        (𝟙_ SymmetricSequence.{u, v}).functor.map degreeUnitIso.inv =
    DayFunctor.ν I PointedCGWH.{u, v}
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => DayFunctor.ν I PointedCGWH.{u, v} ≫ f) hi).trans
      (Category.comp_id _))

/-- The complete original unit comparison is invertible on the full native symmetric diagram. -/
theorem Gη_natTrans_isIso : IsIso (Functor.OplaxMonoidal.η G.{u, v}).natTrans := by
  let : (G.obj (𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}))).functor.IsLeftKanExtension
      GSourceUnit.{u, v} := GSourceUnitIsLeftKan
  exact (Functor.isLeftKanExtension_iff_isIso (Functor.OplaxMonoidal.η G.{u, v}).natTrans
    GSourceUnit.{u, v} (DayFunctor.νNatTrans I PointedCGWH.{u, v}) Gη_fac.{u, v}).1 inferInstance

/-- The actual original symmetrization unit map is an isomorphism of Day functors. -/
theorem Gη_isIso : IsIso (Functor.OplaxMonoidal.η G.{u, v}) := by
  let : IsIso ((DayFunctor.equiv I PointedCGWH.{u, v}).functor.map
      (Functor.OplaxMonoidal.η G.{u, v})) := by
    change IsIso (Functor.OplaxMonoidal.η G.{u, v}).natTrans
    exact Gη_natTrans_isIso.{u, v}
  exact isIso_of_reflects_iso (Functor.OplaxMonoidal.η G.{u, v})
    (DayFunctor.equiv I PointedCGWH.{u, v}).functor

/-- The full original symmetrization is strong monoidal through its actual invertible oplax maps. -/
@[instance_reducible]
def symmetrizationMonoidal : G.{u, v}.Monoidal := by
  let : IsIso (Functor.OplaxMonoidal.η G.{u, v}) := Gη_isIso
  let : ∀ X Y : CategoryTheory.Sequence PointedCGWH.{u, v},
      IsIso (Functor.OplaxMonoidal.δ G X Y) := Gδ_isIso
  exact Functor.Monoidal.ofOplaxMonoidal G.{u, v}

attribute [local instance] symmetrizationMonoidal

/-- The original full Kan adjunction remains monoidal for that same strong structure. -/
theorem sequenceAdjunctionStrongIsMonoidal : sequenceAdjunction.{u, v}.IsMonoidal :=
  sequenceAdjunctionIsMonoidal

/-- The original noncommutative ordered tensor algebra on the one-circle sequence. -/
def orderedSphere : CategoryTheory.Sequence PointedCGWH.{u, v} :=
  CoefficientRestriction.A PointedCGWH.sphereOne.{u, v}

/-- The original ordered concatenation and degree-zero insertion give its actual monoid. -/
@[instance_reducible]
def orderedSphereMonObj : MonObj orderedSphere.{u, v} :=
  CategoryTheory.Sequence.tensorPowerSequenceMonObj PointedCGWH.sphereOne.{u, v}

attribute [local instance] orderedSphereMonObj sphereSequenceMonObj

/-- The full original ordered sphere powers enter the restricted symmetric sphere powers by identity coefficients. -/
def orderedSphereInclusion : orderedSphere.{u, v} ⟶ U.obj sphereSequence.{u, v} :=
  CoefficientRestriction.inclusion PointedCGWH.sphereOne.{u, v}

/-- Every coefficient of the original ordered sphere inclusion is the complete identity on its tensor power. -/
theorem orderedSphereInclusion_app (a : N) : orderedSphereInclusion.{u, v}.natTrans.app a =
    𝟙 (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} (CategoryTheory.Sequence.degree a)) := rfl

/-- The original ordered monoid unit retains the full degree-zero Day generator. -/
theorem orderedSphere_unit_coefficient : DayFunctor.ν N PointedCGWH.{u, v} ≫
    η[orderedSphere.{u, v}].natTrans.app (𝟙_ N) = 𝟙 (𝟙_ PointedCGWH.{u, v}) :=
  CategoryTheory.Sequence.tensorPowerSequenceOne_ν PointedCGWH.sphereOne.{u, v}

/-- The original ordered monoid multiplication retains every full tensor-power concatenation. -/
theorem orderedSphere_pair_coefficient (a b : N) :
    (DayFunctor.η orderedSphere.{u, v} orderedSphere).app (a, b) ≫
      μ[orderedSphere.{u, v}].natTrans.app (a ⊗ b) =
    (TensorPower.tensorPowObj_add PointedCGWH.sphereOne.{u, v}
      (CategoryTheory.Sequence.degree a) (CategoryTheory.Sequence.degree b)).inv := by
  have h := CategoryTheory.Sequence.tensorPowerSequenceMul_η PointedCGWH.sphereOne.{u, v}
    (CategoryTheory.Sequence.degree a) (CategoryTheory.Sequence.degree b)
  change (DayFunctor.η orderedSphere.{u, v} orderedSphere).app (a, b) ≫
      μ[orderedSphere.{u, v}].natTrans.app (a ⊗ b) ≫ orderedSphere.functor.map (𝟙 (a ⊗ b)) =
    TensorPower.laxTensorPowerPairing (𝟭 PointedCGWH.{u, v}) PointedCGWH.sphereOne.{u, v}
      (CategoryTheory.Sequence.degree a) (CategoryTheory.Sequence.degree b) at h
  have hm := orderedSphere.{u, v}.functor.map_id (a ⊗ b)
  have hleg := (congrArg (fun g => (DayFunctor.η orderedSphere.{u, v} orderedSphere).app (a, b) ≫
      μ[orderedSphere.{u, v}].natTrans.app (a ⊗ b) ≫ g) hm).trans
    (congrArg (fun g => (DayFunctor.η orderedSphere.{u, v} orderedSphere).app (a, b) ≫ g)
      (Category.comp_id (μ[orderedSphere.{u, v}].natTrans.app (a ⊗ b))))
  exact hleg.symm.trans (h.trans (Category.id_comp _))

/-- The original symmetric sphere monoid retains the full Day unit coefficient. -/
theorem sphere_unit_coefficient : DayFunctor.ν I PointedCGWH.{u, v} ≫
    η[sphereSequence.{u, v}].natTrans.app (𝟙_ I) = 𝟙 (𝟙_ PointedCGWH.{u, v}) :=
  PointedCGWH.sphereSequence_one_app.{u, v}

/-- The original symmetric sphere multiplication has its original ordered block coefficient. -/
theorem sphere_pair_coefficient (a b : N) :
    (DayFunctor.η sphereSequence.{u, v} sphereSequence).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
      μ[sphereSequence.{u, v}].natTrans.app (degreeInclusion.obj a ⊗ degreeInclusion.obj b) =
    (TensorPower.tensorPowObj_add PointedCGWH.sphereOne.{u, v}
      (CategoryTheory.Sequence.degree a) (CategoryTheory.Sequence.degree b)).inv :=
  PointedCGWH.sphereSequence_mul_app.{u, v} (degreeInclusion.obj a) (degreeInclusion.obj b)

/-- The actual restricted sphere monoid keeps the original degree-zero coefficient insertion. -/
theorem restrictionSphere_unit_coefficient : DayFunctor.ν N PointedCGWH.{u, v} ≫
    η[U.obj sphereSequence.{u, v}].natTrans.app (𝟙_ N) = 𝟙 (𝟙_ PointedCGWH.{u, v}) := by
  change DayFunctor.ν N PointedCGWH.{u, v} ≫ Uε.{u, v}.natTrans.app (𝟙_ N) ≫
      η[sphereSequence.{u, v}].natTrans.app (degreeInclusion.obj (𝟙_ N)) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ η[sphereSequence.{u, v}].natTrans.app (degreeInclusion.obj (𝟙_ N)))
      Uε_unit.{u, v}).trans
        ((congrArg (fun f => f ≫ η[sphereSequence.{u, v}].natTrans.app (degreeInclusion.obj (𝟙_ N)))
          restrictionUnitComponent_eq.{u, v}).trans sphere_unit_coefficient.{u, v}))

/-- The actual restricted sphere monoid keeps every original ordered concatenation coefficient. -/
theorem restrictionSphere_pair_coefficient (a b : N) :
    (DayFunctor.η (U.obj sphereSequence.{u, v}) (U.obj sphereSequence)).app (a, b) ≫
      μ[U.obj sphereSequence.{u, v}].natTrans.app (a ⊗ b) =
    (TensorPower.tensorPowObj_add PointedCGWH.sphereOne.{u, v}
      (CategoryTheory.Sequence.degree a) (CategoryTheory.Sequence.degree b)).inv := by
  change (DayFunctor.η (U.obj sphereSequence.{u, v}) (U.obj sphereSequence)).app (a, b) ≫
      (Uμ sphereSequence.{u, v} sphereSequence).natTrans.app (a ⊗ b) ≫
        μ[sphereSequence.{u, v}].natTrans.app (degreeInclusion.obj (a ⊗ b)) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ μ[sphereSequence.{u, v}].natTrans.app (degreeInclusion.obj (a ⊗ b)))
      (Uμ_pair sphereSequence.{u, v} sphereSequence a b)).trans
        ((congrArg (fun f => f ≫ μ[sphereSequence.{u, v}].natTrans.app (degreeInclusion.obj (a ⊗ b)))
          (restrictionPairComponent_eq sphereSequence.{u, v} sphereSequence a b)).trans
            (sphere_pair_coefficient.{u, v} a b)))

/-- The original inclusion preserves the complete degree-zero monoid coefficient. -/
theorem orderedSphereInclusion_one_coefficient :
    DayFunctor.ν N PointedCGWH.{u, v} ≫ η[orderedSphere.{u, v}].natTrans.app (𝟙_ N) ≫
      orderedSphereInclusion.{u, v}.natTrans.app (𝟙_ N) =
    DayFunctor.ν N PointedCGWH.{u, v} ≫ η[U.obj sphereSequence.{u, v}].natTrans.app (𝟙_ N) := by
  exact (congrArg (fun f => DayFunctor.ν N PointedCGWH.{u, v} ≫ f)
      (Category.comp_id (η[orderedSphere.{u, v}].natTrans.app (𝟙_ N)))).trans
    (orderedSphere_unit_coefficient.{u, v}.trans restrictionSphere_unit_coefficient.{u, v}.symm)

/-- The actual original sphere inclusion preserves the entire ordered monoid unit. -/
theorem orderedSphereInclusion_one_hom : η[orderedSphere.{u, v}] ≫ orderedSphereInclusion.{u, v} =
    η[U.obj sphereSequence.{u, v}] := by
  apply lawfulDay_unit_hom_ext N PointedCGWH.{u, v} (CategoryTheory.Sequence PointedCGWH.{u, v})
  exact orderedSphereInclusion_one_coefficient.{u, v}

/-- Both actual original inclusion coefficients tensor to the full identity on the two sphere powers. -/
theorem orderedSphereInclusion_tensor_identity (a b : N) :
    (orderedSphereInclusion.{u, v}.natTrans.app a ⊗ₘ orderedSphereInclusion.{u, v}.natTrans.app b) =
      𝟙 ((U.obj sphereSequence.{u, v}).functor.obj a ⊗ (U.obj sphereSequence.{u, v}).functor.obj b) :=
  MonoidalCategory.id_tensorHom_id _ _

/-- The original left multiplication composite keeps every full ordered tensor-power coefficient. -/
theorem orderedSphereInclusion_mul_left_coefficient (a b : N) :
    (DayFunctor.η orderedSphere.{u, v} orderedSphere.{u, v}).app (a, b) ≫
      μ[orderedSphere.{u, v}].natTrans.app (a ⊗ b) ≫ orderedSphereInclusion.{u, v}.natTrans.app (a ⊗ b) =
    (TensorPower.tensorPowObj_add PointedCGWH.sphereOne.{u, v}
      (CategoryTheory.Sequence.degree a) (CategoryTheory.Sequence.degree b)).inv :=
  (congrArg (fun f => (DayFunctor.η orderedSphere.{u, v} orderedSphere.{u, v}).app (a, b) ≫ f)
    (Category.comp_id (μ[orderedSphere.{u, v}].natTrans.app (a ⊗ b)))).trans
      (orderedSphere_pair_coefficient.{u, v} a b)

/-- The original right multiplication composite keeps both full inclusion coefficients and their concatenation. -/
theorem orderedSphereInclusion_mul_right_coefficient (a b : N) :
    (orderedSphereInclusion.{u, v}.natTrans.app a ⊗ₘ orderedSphereInclusion.{u, v}.natTrans.app b) ≫
      (DayFunctor.η (U.obj sphereSequence.{u, v}) (U.obj sphereSequence.{u, v})).app (a, b) ≫
        μ[U.obj sphereSequence.{u, v}].natTrans.app (a ⊗ b) =
    (TensorPower.tensorPowObj_add PointedCGWH.sphereOne.{u, v}
      (CategoryTheory.Sequence.degree a) (CategoryTheory.Sequence.degree b)).inv :=
  (congrArg (fun f => f ≫
      (DayFunctor.η (U.obj sphereSequence.{u, v}) (U.obj sphereSequence.{u, v})).app (a, b) ≫
        μ[U.obj sphereSequence.{u, v}].natTrans.app (a ⊗ b))
    (orderedSphereInclusion_tensor_identity.{u, v} a b)).trans
      ((Category.id_comp _).trans (restrictionSphere_pair_coefficient.{u, v} a b))

/-- The original inclusion preserves every full ordered multiplication coefficient. -/
theorem orderedSphereInclusion_mul_coefficient (a b : N) :
    (DayFunctor.η orderedSphere.{u, v} orderedSphere.{u, v}).app (a, b) ≫
      μ[orderedSphere.{u, v}].natTrans.app (a ⊗ b) ≫ orderedSphereInclusion.{u, v}.natTrans.app (a ⊗ b) =
    (orderedSphereInclusion.{u, v}.natTrans.app a ⊗ₘ orderedSphereInclusion.{u, v}.natTrans.app b) ≫
      (DayFunctor.η (U.obj sphereSequence.{u, v}) (U.obj sphereSequence.{u, v})).app (a, b) ≫
        μ[U.obj sphereSequence.{u, v}].natTrans.app (a ⊗ b) :=
  (orderedSphereInclusion_mul_left_coefficient.{u, v} a b).trans
    (orderedSphereInclusion_mul_right_coefficient.{u, v} a b).symm

/-- The actual identity-coefficient inclusion preserves the complete original ordered sphere monoid. -/
instance orderedSphereInclusion_isMonHom : IsMonHom orderedSphereInclusion.{u, v} :=
  CategoryTheory.MonoidalCategory.DayFunctor.Monoid.isMonHom_of_coefficients
    orderedSphere.{u, v} (U.obj sphereSequence.{u, v})
    orderedSphereInclusion.{u, v} orderedSphereInclusion_one_coefficient.{u, v}
      orderedSphereInclusion_mul_coefficient.{u, v}

/-- The actual original inclusion preserves the whole ordered sphere multiplication. -/
theorem orderedSphereInclusion_mul_hom : μ[orderedSphere.{u, v}] ≫ orderedSphereInclusion.{u, v} =
    (orderedSphereInclusion.{u, v} ⊗ₘ orderedSphereInclusion.{u, v}) ≫ μ[U.obj sphereSequence.{u, v}] :=
  IsMonHom.mul_hom orderedSphereInclusion.{u, v}

/-- The original ordered sphere tensor algebra, bundled with its actual multiplication. -/
def orderedSphereMon : Mon (CategoryTheory.Sequence PointedCGWH.{u, v}) :=
  { X := orderedSphere.{u, v}, mon := orderedSphereMonObj.{u, v} }

/-- The original symmetric sphere monoid, bundled with the selected full permutation multiplication. -/
def sphereMon : Mon SymmetricSequence.{u, v} :=
  { X := sphereSequence.{u, v}, mon := sphereSequenceMonObj.{u, v} }

/-- The original coefficient inclusion is a complete monoid morphism before transposition. -/
def orderedSphereInclusionMonoid : orderedSphereMon.{u, v} ⟶ (Functor.mapMon U.{u, v}).obj sphereMon.{u, v} :=
  { hom := orderedSphereInclusion.{u, v}, isMonHom_hom := orderedSphereInclusion_isMonHom.{u, v} }

/-- The original monoid inclusion retains its independently typed whole underlying map. -/
theorem orderedSphereInclusionMonoid_hom : orderedSphereInclusionMonoid.{u, v}.hom =
    orderedSphereInclusion.{u, v} := rfl

/-- The original tensor-algebra-to-symmetric-algebra map is the actual monoid-adjunction transpose. -/
def tensorSphereMonoidMap : (Functor.mapMon G.{u, v}).obj orderedSphereMon.{u, v} ⟶ sphereMon.{u, v} :=
  (sequenceAdjunction.{u, v}.mapMon.homEquiv orderedSphereMon.{u, v} sphereMon.{u, v}).symm
    orderedSphereInclusionMonoid.{u, v}

/-- The same original algebra map on the independently typed native symmetrization carrier. -/
def tensorSphereMap : G.obj orderedSphere.{u, v} ⟶ sphereSequence.{u, v} := tensorSphereMonoidMap.{u, v}.hom

/-- The original full algebra map preserves the original unit and multiplication. -/
instance tensorSphereMap_isMonHom : IsMonHom tensorSphereMap.{u, v} :=
  tensorSphereMonoidMap.{u, v}.isMonHom_hom

/-- The monoid-adjunction counit keeps the original underlying full Kan counit. -/
theorem sphereMonoidCounit_hom : (sequenceAdjunction.{u, v}.mapMon.counit.app sphereMon.{u, v}).hom =
    sequenceAdjunction.counit.app sphereSequence.{u, v} := by
  change 𝟙 (G.obj (U.obj sphereSequence.{u, v})) ≫
      sequenceAdjunction.counit.app sphereSequence ≫ 𝟙 sphereSequence = _
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The actual algebra map is the original inverse Kan Hom function on the original inclusion. -/
theorem tensorSphereMap_original : tensorSphereMap.{u, v} =
    (sequenceAdjunction.{u, v}.homEquiv orderedSphere.{u, v} sphereSequence.{u, v}).symm
      orderedSphereInclusion.{u, v} := by
  rw [sequenceAdjunction.{u, v}.homEquiv_counit]
  have h :=
    congrArg (fun f : (Functor.mapMon G.{u, v}).obj orderedSphereMon.{u, v} ⟶ sphereMon.{u, v} => f.hom)
      (sequenceAdjunction.{u, v}.mapMon.homEquiv_counit orderedSphereMon.{u, v} sphereMon.{u, v}
        orderedSphereInclusionMonoid.{u, v})
  simp only [Mon.comp_hom', Functor.mapMon_map_hom] at h
  rw [orderedSphereInclusionMonoid_hom] at h
  exact h.trans (congrArg (fun f => G.map orderedSphereInclusion.{u, v} ≫ f)
    sphereMonoidCounit_hom.{u, v})

/-- The complete original algebra map transposes back to the full ordered coefficient inclusion. -/
theorem tensorSphereMap_unit : sequenceAdjunction.unit.app orderedSphere.{u, v} ≫
    U.map tensorSphereMap.{u, v} = orderedSphereInclusion.{u, v} := by
  have h : sequenceAdjunction.homEquiv orderedSphere.{u, v} sphereSequence.{u, v} tensorSphereMap.{u, v} =
      orderedSphereInclusion.{u, v} :=
    (congrArg (sequenceAdjunction.homEquiv orderedSphere.{u, v} sphereSequence.{u, v})
      tensorSphereMap_original.{u, v}).trans
      ((sequenceAdjunction.homEquiv orderedSphere.{u, v} sphereSequence.{u, v}).apply_symm_apply
        orderedSphereInclusion.{u, v})
  exact (sequenceAdjunction.homEquiv_unit orderedSphere.{u, v} sphereSequence.{u, v}
    tensorSphereMap.{u, v}).symm.trans h

/-- Every original tensor-algebra coefficient is sent to its original full sphere permutation map. -/
@[reassoc]
theorem tensorSphereMap_coefficient (n : N) (m : I) (σ : degreeInclusion.obj n ⟶ m) :
    coefficient orderedSphere.{u, v} n m σ ≫ tensorSphereMap.natTrans.app m =
      sphereSequence.{u, v}.functor.map σ := by
  have hu : (sequenceAdjunction.unit.app orderedSphere.{u, v}).natTrans.app n ≫
      tensorSphereMap.natTrans.app (degreeInclusion.obj n) = orderedSphereInclusion.natTrans.app n :=
    congrArg (fun f => f.natTrans.app n) tensorSphereMap_unit.{u, v}
  rw [GUnit_original] at hu
  have hn := tensorSphereMap.{u, v}.natTrans.naturality σ
  change (GUnit orderedSphere.{u, v}).app n ≫ (G.obj orderedSphere).functor.map σ ≫
      tensorSphereMap.natTrans.app m = sphereSequence.functor.map σ
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (GUnit orderedSphere.{u, v}).app n ≫ f) hn).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ sphereSequence.{u, v}.functor.map σ) hu).trans
          (Category.id_comp _))))

/-- The complete original tensor algebra functor on the freely symmetrized degree-one generators. -/
def tensorAlgebraFunctor : PointedCGWH.{u, v} ⥤ Mon SymmetricSequence.{u, v} :=
  CategoryTheory.Sequence.OrderedTensorAlgebra.freeFunctor ⋙ Functor.mapMon G.{u, v}

/-- The complete original symmetric generator functor, with its actual ordinary free-at-one and Kan maps. -/
def degreeOneGeneratorFunctor : PointedCGWH.{u, v} ⥤ SymmetricSequence.{u, v} :=
  CategoryTheory.Sequence.freeAt PointedCGWH.{u, v} 1 ⋙ G.{u, v}

/-- The original tensor algebra on every actual degree-one coefficient. -/
def tensorAlgebra (K : PointedCGWH.{u, v}) : Mon SymmetricSequence.{u, v} := tensorAlgebraFunctor.obj K

/-- The freely symmetrized original degree-one sequence at every pointed coefficient. -/
def degreeOneGenerator (K : PointedCGWH.{u, v}) : SymmetricSequence.{u, v} := degreeOneGeneratorFunctor.obj K

/-- The actual whole coefficient evaluation underlying the tensor-algebra adjunction. -/
def tensorAlgebraEvaluation : Mon SymmetricSequence.{u, v} ⥤ PointedCGWH.{u, v} where
  obj M := M.X.functor.obj (card 1)
  map f := f.hom.natTrans.app (card 1)

/-- The full original evaluation keeps every object, arrow and functor law of the two original stages. -/
private theorem tensorAlgebraEvaluation_original_data : tensorAlgebraEvaluation.{u, v} =
    Functor.mapMon U.{u, v} ⋙ CategoryTheory.Sequence.OrderedTensorAlgebra.generatorEvaluation := rfl

/-- The whole original coefficient evaluation underlying the degree-one generator adjunction. -/
def degreeOneGeneratorEvaluation : SymmetricSequence.{u, v} ⥤ PointedCGWH.{u, v} :=
  U.{u, v} ⋙ CategoryTheory.Sequence.evaluation PointedCGWH.{u, v} 1

/-- The genuine ordered free adjunction followed by the full original monoid Kan adjunction. -/
def tensorAlgebraAdjunction : tensorAlgebraFunctor.{u, v} ⊣ tensorAlgebraEvaluation.{u, v} :=
  CategoryTheory.Sequence.OrderedTensorAlgebra.freeAdjunction.comp sequenceAdjunction.{u, v}.mapMon

/-- The original ordinary degree-one free adjunction followed by the full original Kan adjunction. -/
def degreeOneGeneratorAdjunction :
    degreeOneGeneratorFunctor.{u, v} ⊣ degreeOneGeneratorEvaluation.{u, v} :=
  (CategoryTheory.Sequence.freeAtEvaluationAdjunction PointedCGWH.{u, v} 1).comp
    sequenceAdjunction.{u, v}

/-- Both entire original Hom functions prove the genuine tensor-algebra generator universal property. -/
def tensorAlgebraHomEquiv (K : PointedCGWH.{u, v}) (M : Mon SymmetricSequence.{u, v}) :
    (tensorAlgebra K ⟶ M) ≃ (degreeOneGenerator K ⟶ M.X) :=
  (tensorAlgebraAdjunction.homEquiv K M).trans
    (degreeOneGeneratorAdjunction.homEquiv K M.X).symm

/-- The complete forward and inverse tensor-algebra Hom functions recover every original monoid map. -/
theorem tensorAlgebraHomEquiv_left_inverse (K : PointedCGWH.{u, v}) (M : Mon SymmetricSequence.{u, v})
    (f : tensorAlgebra K ⟶ M) :
    (tensorAlgebraHomEquiv K M).symm (tensorAlgebraHomEquiv K M f) = f :=
  (tensorAlgebraHomEquiv K M).symm_apply_apply f

/-- The complete inverse and forward tensor-algebra Hom functions recover every original generator map. -/
theorem tensorAlgebraHomEquiv_right_inverse (K : PointedCGWH.{u, v}) (M : Mon SymmetricSequence.{u, v})
    (g : degreeOneGenerator K ⟶ M.X) :
    tensorAlgebraHomEquiv K M ((tensorAlgebraHomEquiv K M).symm g) = g :=
  (tensorAlgebraHomEquiv K M).apply_symm_apply g

/-- Every original target monoid arrow preserves the entire tensor-algebra generator correspondence. -/
theorem tensorAlgebraHomEquiv_natural_target (K : PointedCGWH.{u, v})
    {M Q : Mon SymmetricSequence.{u, v}} (f : tensorAlgebra K ⟶ M) (h : M ⟶ Q) :
    tensorAlgebraHomEquiv K Q (f ≫ h) = tensorAlgebraHomEquiv K M f ≫ h.hom := by
  have hT := tensorAlgebraAdjunction.{u, v}.homEquiv_naturality_right f h
  have hG := degreeOneGeneratorAdjunction.{u, v}.homEquiv_naturality_right_symm
    (tensorAlgebraAdjunction.homEquiv K M f) h.hom
  exact (congrArg (degreeOneGeneratorAdjunction.homEquiv K Q.X).symm hT).trans hG

/-- Every original coefficient arrow preserves the entire tensor-algebra generator correspondence. -/
theorem tensorAlgebraHomEquiv_natural_source {K L : PointedCGWH.{u, v}} (h : K ⟶ L)
    (M : Mon SymmetricSequence.{u, v}) (f : tensorAlgebra L ⟶ M) :
    tensorAlgebraHomEquiv K M (tensorAlgebraFunctor.map h ≫ f) =
      degreeOneGeneratorFunctor.map h ≫ tensorAlgebraHomEquiv L M f := by
  have hT := tensorAlgebraAdjunction.{u, v}.homEquiv_naturality_left h f
  have hG := degreeOneGeneratorAdjunction.{u, v}.homEquiv_naturality_left_symm
    h (tensorAlgebraAdjunction.homEquiv L M f)
  exact (congrArg (degreeOneGeneratorAdjunction.homEquiv K M.X).symm hT).trans hG


/-- The complete original degree-one insertion into the genuine tensor algebra. -/
def tensorAlgebraGenerator (K : PointedCGWH.{u, v}) :
    degreeOneGenerator K ⟶ (tensorAlgebra K).X :=
  tensorAlgebraHomEquiv K (tensorAlgebra K) (𝟙 (tensorAlgebra K))

/-- Every full original monoid map is evaluated by the same actual generator insertion. -/
theorem tensorAlgebraHomEquiv_generator (K : PointedCGWH.{u, v})
    (M : Mon SymmetricSequence.{u, v}) (f : tensorAlgebra K ⟶ M) :
    tensorAlgebraHomEquiv K M f = tensorAlgebraGenerator K ≫ f.hom := by
  have h := tensorAlgebraHomEquiv_natural_target K (𝟙 (tensorAlgebra K)) f
  exact (congrArg (tensorAlgebraHomEquiv K M) (Category.id_comp f)).symm.trans h

/-- The original circle tensor algebra is the same whole symmetrized ordered sphere monoid. -/
theorem tensorAlgebraCircle_original :
    tensorAlgebra PointedCGWH.sphereOne.{u, v} =
      (Functor.mapMon G.{u, v}).obj orderedSphereMon.{u, v} := rfl

/-- The genuine tensor-algebra adjunction keeps both complete original Hom stages. -/
theorem tensorAlgebraAdjunction_forward (K : PointedCGWH.{u, v})
    (M : Mon SymmetricSequence.{u, v}) (f : tensorAlgebra K ⟶ M) :
    tensorAlgebraAdjunction.homEquiv K M f =
      CategoryTheory.Sequence.OrderedTensorAlgebra.freeAdjunction.homEquiv K ((Functor.mapMon U.{u, v}).obj M)
        (sequenceAdjunction.{u, v}.mapMon.homEquiv
          (CategoryTheory.Sequence.OrderedTensorAlgebra.freeMonoid K) M f) := by
  have h := Adjunction.comp_homEquiv CategoryTheory.Sequence.OrderedTensorAlgebra.freeAdjunction
    sequenceAdjunction.{u, v}.mapMon
  exact congrArg (fun e => e f) (congrFun (congrFun h K) M)

/-- The actual original tensor-algebra map retrieves the complete original circle generator. -/
theorem tensorSphereMap_generator :
    tensorAlgebraAdjunction.homEquiv PointedCGWH.sphereOne.{u, v}
      sphereMon.{u, v} tensorSphereMonoidMap.{u, v} = (λ_ PointedCGWH.sphereOne.{u, v}).inv := by
  have h₀ := tensorAlgebraAdjunction_forward PointedCGWH.sphereOne.{u, v}
    sphereMon.{u, v} tensorSphereMonoidMap.{u, v}
  have h₁ : sequenceAdjunction.{u, v}.mapMon.homEquiv orderedSphereMon.{u, v} sphereMon.{u, v}
      tensorSphereMonoidMap.{u, v} = orderedSphereInclusionMonoid.{u, v} :=
    (sequenceAdjunction.{u, v}.mapMon.homEquiv orderedSphereMon.{u, v} sphereMon.{u, v}).apply_symm_apply
      orderedSphereInclusionMonoid.{u, v}
  have h₂ := CategoryTheory.Sequence.OrderedTensorAlgebra.freeAdjunction_homEquiv PointedCGWH.sphereOne.{u, v}
    ((Functor.mapMon U.{u, v}).obj sphereMon.{u, v})
  have h₃ : CategoryTheory.Sequence.OrderedTensorAlgebra.generatorHomEquiv PointedCGWH.sphereOne.{u, v}
      ((Functor.mapMon U.{u, v}).obj sphereMon.{u, v}) orderedSphereInclusionMonoid.{u, v} =
      (λ_ PointedCGWH.sphereOne.{u, v}).inv := by
    change (λ_ PointedCGWH.sphereOne.{u, v}).inv ≫
      𝟙 (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} 1) = _
    exact Category.comp_id _
  exact h₀.trans
    ((congrArg (CategoryTheory.Sequence.OrderedTensorAlgebra.freeAdjunction.homEquiv PointedCGWH.sphereOne.{u, v}
      ((Functor.mapMon U.{u, v}).obj sphereMon.{u, v})) h₁).trans
        ((congrArg (fun e => e orderedSphereInclusionMonoid.{u, v}) h₂).trans h₃))

/-- The source circle enters the original symmetric sphere through the actual degree-one free adjunction. -/
def symmetricSphereGenerator : degreeOneGenerator PointedCGWH.sphereOne.{u, v} ⟶
    sphereSequence.{u, v} :=
  (degreeOneGeneratorAdjunction.homEquiv PointedCGWH.sphereOne.{u, v} sphereSequence.{u, v}).symm
    (λ_ PointedCGWH.sphereOne.{u, v}).inv

/-- The original complete algebra map is exactly the monoid extension of the original sphere generator. -/
theorem tensorSphereMap_free_generator :
    tensorAlgebraHomEquiv PointedCGWH.sphereOne.{u, v} sphereMon.{u, v}
      tensorSphereMonoidMap.{u, v} = symmetricSphereGenerator.{u, v} :=
  congrArg
    (degreeOneGeneratorAdjunction.homEquiv PointedCGWH.sphereOne.{u, v} sphereSequence.{u, v}).symm
    tensorSphereMap_generator.{u, v}


attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf

/-- The actual original Day end adjunction supplies the full symmetric-sequence closed structure. -/
@[instance_reducible]
def symmetricSequenceClosed : MonoidalClosed SymmetricSequence.{u, v} := inferInstance

/-- The actual ordinary Day equivalence transports every original small pointwise sequence colimit. -/
theorem symmetricSequenceColimits : HasColimitsOfSize.{0, 0} SymmetricSequence.{u, v} :=
  Adjunction.has_colimits_of_equivalence (DayFunctor.equiv I PointedCGWH.{u, v}).functor

attribute [local instance] symmetricSequenceClosed symmetricSequenceColimits

/-- Every original Day tensor-left functor preserves the same complete native small colimits. -/
theorem symmetricTensorLeftPreservesColimits (X : SymmetricSequence.{u, v}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft X) := inferInstance

attribute [local instance] symmetricTensorLeftPreservesColimits

/-- The original structural/module and enriched/structural equivalences keep the full native sequential carrier. -/
def sequentialModuleEquivalence : NativeIndexKanComposition.SequentialCarrier.{u, v} ≌
    Mod (CategoryTheory.Sequence PointedCGWH.{u, v}) orderedSphere.{u, v} :=
  (CategoryTheory.SequentialSpectrum.EnrichedPresentation.enrichedEquivalence
    PointedCGWH.sphereOne.{u, v}).symm.trans
      (CategoryTheory.SequentialSpectrum.moduleEquivalence PointedCGWH.sphereOne.{u, v})

/-- The actual monoidal module lift followed by the original balanced scalar induction. -/
def moduleInduction : Mod (CategoryTheory.Sequence PointedCGWH.{u, v}) orderedSphere.{u, v} ⥤
    Mod SymmetricSequence.{u, v} sphereSequence.{u, v} :=
  Functor.mapMod G.{u, v} orderedSphere.{u, v} ⋙
    Mod.ExtensionOfScalars.induction tensorSphereMap.{u, v}

/-- The complete restriction retains the original scalar map and the full monoidal-adjunction unit. -/
def moduleRestriction : Mod SymmetricSequence.{u, v} sphereSequence.{u, v} ⥤
    Mod (CategoryTheory.Sequence PointedCGWH.{u, v}) orderedSphere.{u, v} :=
  monoidalScalarRestriction sequenceAdjunction.{u, v} orderedSphere.{u, v} tensorSphereMap.{u, v}

/-- Both original module Hom functions give the full balanced induction/restriction adjunction. -/
def moduleAdjunction : moduleInduction.{u, v} ⊣ moduleRestriction.{u, v} :=
  (Mod.MonoidalAdjunction.adjunction sequenceAdjunction.{u, v} orderedSphere.{u, v}).comp
    (Mod.ExtensionOfScalars.adjunction tensorSphereMap.{u, v})

/-- The actual native induction uses the full original module/operator equivalences and the genuine balanced tensor. -/
def V : NativeIndexKanComposition.SequentialCarrier.{u, v} ⥤ NativeIndexKanComposition.SymmetricCarrier.{u, v} :=
  sequentialModuleEquivalence.{u, v}.functor ⋙ moduleInduction.{u, v} ⋙
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor

/-- The original right functor uses both full carrier equivalences and the same actual module restriction. -/
def W : NativeIndexKanComposition.SymmetricCarrier.{u, v} ⥤ NativeIndexKanComposition.SequentialCarrier.{u, v} :=
  PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse ⋙
    moduleRestriction.{u, v} ⋙ sequentialModuleEquivalence.{u, v}.inverse

/-- The complete original balanced induction functor has its full native adjunction. -/
def VWAdjunction : V.{u, v} ⊣ W.{u, v} :=
  (sequentialModuleEquivalence.{u, v}.toAdjunction.comp moduleAdjunction.{u, v}).comp
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.toAdjunction

/-- The complete module restriction keeps the same original ordered coefficient diagram. -/
theorem moduleRestriction_carrier (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    ((moduleRestriction.{u, v}).obj M).X = U.obj M.X := rfl

/-- Every original module-restriction arrow is the identical ordered restriction arrow. -/
theorem moduleRestriction_map {M Q : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}} (f : M ⟶ Q) :
    ((moduleRestriction.{u, v}).map f).hom = U.map f.hom := rfl

/-- The whole actual module action is the original ordered sphere inclusion followed by its native pair action. -/
theorem moduleRestriction_action (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    ((moduleRestriction.{u, v}).obj M).mod.smul =
      (orderedSphereInclusion.{u, v} ▷ U.obj M.X) ≫ Uμ sphereSequence.{u, v} M.X ≫ U.map M.mod.smul := by
  have h := monoidalScalarRestriction_action sequenceAdjunction.{u, v} orderedSphere.{u, v}
    tensorSphereMap.{u, v} M
  rw [tensorSphereMap_unit] at h
  exact h

/-- The original two restriction stages supply the unit law for the complete direct action. -/
theorem directRestrictionModule_one (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    (η[orderedSphere.{u, v}] ▷ U.obj M.X) ≫
        CoefficientRestriction.moduleAction PointedCGWH.sphereOne.{u, v} M.X M.mod.smul =
      (λ_ (U.obj M.X)).hom :=
  ((Functor.mapMod U.{u, v} sphereSequence.{u, v} ⋙
    Mod.comap orderedSphereInclusion.{u, v}).obj M).mod.one_smul

/-- The original two restriction stages supply associativity for the complete direct action. -/
theorem directRestrictionModule_mul (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    (μ[orderedSphere.{u, v}] ▷ U.obj M.X) ≫
        CoefficientRestriction.moduleAction PointedCGWH.sphereOne.{u, v} M.X M.mod.smul =
      (α_ orderedSphere.{u, v} orderedSphere.{u, v} (U.obj M.X)).hom ≫
        (orderedSphere.{u, v} ◁
          CoefficientRestriction.moduleAction PointedCGWH.sphereOne.{u, v} M.X M.mod.smul) ≫
        CoefficientRestriction.moduleAction PointedCGWH.sphereOne.{u, v} M.X M.mod.smul :=
  ((Functor.mapMod U.{u, v} sphereSequence.{u, v} ⋙
    Mod.comap orderedSphereInclusion.{u, v}).obj M).mod.mul_smul

/-- The actual original restricted module, with its same action stored before any field is projected. -/
def directRestrictionModule (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    Mod (CategoryTheory.Sequence PointedCGWH.{u, v}) orderedSphere.{u, v} := by
  letI : MonObj (CoefficientRestriction.A PointedCGWH.sphereOne.{u, v}) := orderedSphereMonObj.{u, v}
  exact CoefficientRestriction.moduleData PointedCGWH.sphereOne.{u, v} M.X M.mod.smul
    (((Functor.mapMod U.{u, v} sphereSequence.{u, v} ⋙
      Mod.comap orderedSphereInclusion.{u, v}).obj M).mod.one_smul)
    (((Functor.mapMod U.{u, v} sphereSequence.{u, v} ⋙
      Mod.comap orderedSphereInclusion.{u, v}).obj M).mod.mul_smul)

/-- The full direct module is the public coefficient-restriction constructor with its original laws. -/
theorem directRestrictionModule_original
    (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    letI : MonObj (CoefficientRestriction.A PointedCGWH.sphereOne.{u, v}) := orderedSphereMonObj.{u, v}
    directRestrictionModule M =
      CoefficientRestriction.moduleData PointedCGWH.sphereOne.{u, v} M.X M.mod.smul
        (directRestrictionModule_one M) (directRestrictionModule_mul M) := rfl

/-- The public direct-module constructor retains the entire original restricted carrier. -/
theorem directRestrictionModule_carrier
    (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    (directRestrictionModule M).X = U.obj M.X := rfl

/-- The original direct restriction uses the same full ordered sphere map on the actual restricted module. -/
def directModuleRestriction : Mod SymmetricSequence.{u, v} sphereSequence.{u, v} ⥤
    Mod (CategoryTheory.Sequence PointedCGWH.{u, v}) orderedSphere.{u, v} where
  obj := directRestrictionModule.{u, v}
  map f :=
    { hom := U.map f.hom
      isModHom := ((Functor.mapMod U.{u, v} sphereSequence.{u, v} ⋙
        Mod.comap orderedSphereInclusion.{u, v}).map f).isModHom }
  map_id M := by
    apply Mod.hom_ext
    exact U.map_id M.X
  map_comp f g := by
    apply Mod.hom_ext
    exact U.map_comp f.hom g.hom

/-- Every original module action and map is the same as the full composition of the two restriction stages. -/
theorem directModuleRestriction_original : directModuleRestriction.{u, v} =
    Functor.mapMod U.{u, v} sphereSequence.{u, v} ⋙ Mod.comap orderedSphereInclusion.{u, v} := rfl

/-- The direct original restriction retains that same complete action. -/
theorem directModuleRestriction_action (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    ((directModuleRestriction.{u, v}).obj M).mod.smul =
      (orderedSphereInclusion.{u, v} ▷ U.obj M.X) ≫ Uμ sphereSequence.{u, v} M.X ≫ U.map M.mod.smul := rfl

/-- Both complete module restrictions are compared by the original identity on every ordered diagram. -/
def moduleRestrictionIso : moduleRestriction.{u, v} ≅ directModuleRestriction.{u, v} :=
  NatIso.ofComponents
    (fun M => Mod.isoOfUnderlyingIso (Iso.refl (U.obj M.X)) (by
      change ((moduleRestriction.{u, v}).obj M).mod.smul ≫ 𝟙 (U.obj M.X) =
        (orderedSphere.{u, v} ◁ 𝟙 (U.obj M.X)) ≫ ((directModuleRestriction.{u, v}).obj M).mod.smul
      have hi := MonoidalCategory.whiskerLeft_id orderedSphere.{u, v} (U.obj M.X)
      exact (Category.comp_id ((moduleRestriction.{u, v}).obj M).mod.smul).trans
        (((moduleRestriction_action M).trans (directModuleRestriction_action M).symm).trans
          ((Category.id_comp ((directModuleRestriction.{u, v}).obj M).mod.smul).symm.trans
            (congrArg (fun f => f ≫ ((directModuleRestriction.{u, v}).obj M).mod.smul) hi.symm)))))
    (by
      intro M Q f
      apply Mod.hom_ext
      change ((moduleRestriction.{u, v}).map f).hom ≫ 𝟙 (U.obj Q.X) =
        𝟙 (U.obj M.X) ≫ ((directModuleRestriction.{u, v}).map f).hom
      rw [moduleRestriction_map]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)


end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
