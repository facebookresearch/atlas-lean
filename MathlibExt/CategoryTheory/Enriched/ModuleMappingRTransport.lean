/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

module

public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRSelectedSource
public import MathlibExt.CategoryTheory.Monoidal.Transport

/-!
# Transported tensor projections for source right modules

The source quotient, coend generators, naturality, and braiding retain
the complete coefficient and equivalence data at independent universes.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.Enriched CategoryTheory.EnrichedDayKernel
open CategoryTheory.Monoidal.Transport
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.ModuleMappingRTransport

namespace Coend
universe uV vV uI vI
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (B : EnrichedFunctor.LaxBraidedData L)

section CoendMaps

include b B in
/-- The complete original continuous Day generator followed by the actual scalar quotient. -/
def coendGenerator :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    letI := EnrichedDayKernel.BraidingMonoidal.symmetricCategory d b
    letI := EnrichedDayKernel.LaxMonoid.monObj d S L
    letI := EnrichedDayKernel.LaxMonoid.isCommMonObj d b S L B
    letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
    letI : ∀ X : EnrichedFunctorCat V I,
        PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
      (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).1
    letI : ∀ X : EnrichedFunctorCat V I,
        PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
      (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).2
    letI : MonoidalCategory (CommutativeModuleConversion.RightModule
      (⟨S⟩ : EnrichedFunctorCat V I)) :=
      RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ (X Y : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (k : I) (a : I × I),
      EnrichedDayKernel.objects d.tensorEnrichedFunctor
          X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a ⟶
        (X ⊗ Y).X.toEnrichedFunctor.obj k := by
  let q : ModuleMappingR.SelectedSource V I := {
    monoidalData := d
    braidedData := b
    coefficientFunctor := S
    coefficientMonoidal := L
    coefficientBraided := B }
  exact q.coendGenerator

include b B in
/-- Every original coefficient and both whole input maps are retained by the scalar smash map. -/
theorem coendGenerator_map :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    letI := EnrichedDayKernel.BraidingMonoidal.symmetricCategory d b
    letI := EnrichedDayKernel.LaxMonoid.monObj d S L
    letI := EnrichedDayKernel.LaxMonoid.isCommMonObj d b S L B
    letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
    letI : ∀ X : EnrichedFunctorCat V I,
        PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
      (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).1
    letI : ∀ X : EnrichedFunctorCat V I,
        PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
      (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).2
    letI : MonoidalCategory (CommutativeModuleConversion.RightModule
      (⟨S⟩ : EnrichedFunctorCat V I)) :=
      RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ {X X' Y Y' : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I)}
      (f : X ⟶ X') (g : Y ⟶ Y') (k : I) (a : I × I),
      coendGenerator d b S L B X Y k a ≫
          EnrichedFunctorCat.component (f ⊗ₘ g).hom k =
        (𝟙 (d.tensorEnrichedFunctor.obj a ⟶[V] k) ⊗ₘ
          (EnrichedFunctorCat.component f.hom a.1 ⊗ₘ
            EnrichedFunctorCat.component g.hom a.2)) ≫
          coendGenerator d b S L B X' Y' k a := by
  let q : ModuleMappingR.SelectedSource V I := {
    monoidalData := d
    braidedData := b
    coefficientFunctor := S
    coefficientMonoidal := L
    coefficientBraided := B }
  intro X X' Y Y' f g k a
  exact q.coendGenerator_map f g k a

include b B in
/-- The complete canonical generator formula on the original full source-module types. -/
theorem coendGenerator_formula :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    letI := EnrichedDayKernel.BraidingMonoidal.symmetricCategory d b
    letI := EnrichedDayKernel.LaxMonoid.monObj d S L
    letI := EnrichedDayKernel.LaxMonoid.isCommMonObj d b S L B
    letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
    letI : ∀ X : EnrichedFunctorCat V I,
        PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
      (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).1
    letI : ∀ X : EnrichedFunctorCat V I,
        PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
      (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).2
    letI : MonoidalCategory (CommutativeModuleConversion.RightModule
      (⟨S⟩ : EnrichedFunctorCat V I)) :=
      RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ (X Y : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (k : I) (a : I × I),
      coendGenerator d b S L B X Y k a =
        EnrichedDayKernel.gen d.tensorEnrichedFunctor
          X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a ≫
            EnrichedFunctorCat.component
              (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) X Y) k := by
  let := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
  let := EnrichedDayKernel.BraidingMonoidal.symmetricCategory d b
  let := EnrichedDayKernel.LaxMonoid.monObj d S L
  let := EnrichedDayKernel.LaxMonoid.isCommMonObj d b S L B
  let : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).1
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).2
  let : MonoidalCategory (CommutativeModuleConversion.RightModule
    (⟨S⟩ : EnrichedFunctorCat V I)) :=
    RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  let q : ModuleMappingR.SelectedSource V I := {
    monoidalData := d
    braidedData := b
    coefficientFunctor := S
    coefficientMonoidal := L
    coefficientBraided := B }
  exact q.coendGenerator_formula

end CoendMaps

end Coend

namespace Quotient
universe uV vV uI vI uD vD
open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.Enriched CategoryTheory.EnrichedDayKernel
attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (B : EnrichedFunctor.LaxBraidedData L)
  {D : Type uD} [Category.{vD} D]

/-- The complete original projection function type, at actual source and native tensor data. -/
def ProjectionFamily (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D) : Type _ :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  letI := ModuleMappingR.moduleMonoidal d b S L B
  letI := tensor
  ∀ (X Y : D), (E.inverse.obj X).X ⊗ (E.inverse.obj Y).X ⟶ (E.inverse.obj (X ⊗ Y)).X

/-- The original quotient is followed by the entire actual source comparison map. -/
def originalProjection (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (comparison : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.IsoFamily E tensor) : ProjectionFamily d S L E tensor :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  letI := ModuleMappingR.moduleMonoidal d b S L B
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI := LaxMonoid.isCommMonObj d b S L B
  letI := tensor
  fun X Y =>
    RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
      (E.inverse.obj X) (E.inverse.obj Y) ≫
    (comparison X Y).hom.hom

/-- The complete original weighted isometry generator type, at every X/Y/k/a. -/
def GeneratorFamily (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D) : Type _ :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  letI := ModuleMappingR.moduleMonoidal d b S L B
  letI := tensor
  ∀ (X Y : D) (k : I) (a : I × I),
    EnrichedDayKernel.objects d.tensorEnrichedFunctor (E.inverse.obj X).X.toEnrichedFunctor
      (E.inverse.obj Y).X.toEnrichedFunctor k a ⟶ (E.inverse.obj (X ⊗ Y)).X.toEnrichedFunctor.obj k

/-- Every original source coend generator keeps the whole original comparison component. -/
def originalGenerator (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (comparison : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.IsoFamily E tensor) : GeneratorFamily d S L E tensor :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  letI := ModuleMappingR.moduleMonoidal d b S L B
  letI := tensor
  fun X Y k a => Coend.coendGenerator
    d b S L B (E.inverse.obj X) (E.inverse.obj Y) k a ≫
      EnrichedFunctorCat.component (comparison X Y).hom.hom k

/-- The complete original projection equation at every source/target/isometry integrand. -/
def GeneratorProjectionFormula (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (comparison : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.IsoFamily E tensor) (X Y : D) (k : I) (a : I × I) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  letI := ModuleMappingR.moduleMonoidal d b S L B
  letI := tensor
  originalGenerator d b S L B E tensor comparison X Y k a =
    EnrichedDayKernel.gen d.tensorEnrichedFunctor (E.inverse.obj X).X.toEnrichedFunctor
      (E.inverse.obj Y).X.toEnrichedFunctor k a ≫
      EnrichedFunctorCat.component (originalProjection d b S L B E tensor comparison X Y) k

/-- Both complete parent suppliers retain the original generator-followed-by-projection word. -/
theorem generatorProjection_original (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (comparison : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.IsoFamily E tensor) (X Y : D) (k : I) (a : I × I) :
    GeneratorProjectionFormula d b S L B E tensor comparison X Y k a := by
  let := ColimitMonoidal.monoidalCategory d
  let := LaxMonoid.monObj d S L
  let := ModuleMappingR.moduleMonoidal d b S L B
  let := tensor
  simp only [GeneratorProjectionFormula, originalGenerator, originalProjection,
    Coend.coendGenerator_formula,
    EnrichedFunctorCat.component_comp, Category.assoc]

/-- The complete original balancing relation on every pair of full continuous Day coefficients. -/
def BalancedFormula (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (comparison : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.IsoFamily E tensor) (X Y : D) (k : I) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  letI := ModuleMappingR.moduleMonoidal d b S L B
  letI := tensor
  EnrichedDayKernel.Balanced d.tensorEnrichedFunctor (E.inverse.obj X).X.toEnrichedFunctor
    (E.inverse.obj Y).X.toEnrichedFunctor k (originalGenerator d b S L B E tensor comparison X Y k)

/-- Every original Day relation survives both the original source quotient and comparison. -/
theorem balanced_original (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (comparison : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.IsoFamily E tensor) (X Y : D) (k : I) :
    BalancedFormula d b S L B E tensor comparison X Y k := by
  let := ColimitMonoidal.monoidalCategory d
  let := LaxMonoid.monObj d S L
  let := ModuleMappingR.moduleMonoidal d b S L B
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let := LaxMonoid.isCommMonObj d b S L B
  let := tensor
  intro a a'
  simpa only [BalancedFormula, originalGenerator,
    Coend.coendGenerator_formula,
    Category.assoc] using
    congrArg (fun q => q ≫
      EnrichedFunctorCat.component
        (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
          (E.inverse.obj X) (E.inverse.obj Y)) k ≫
      EnrichedFunctorCat.component (comparison X Y).hom.hom k)
      (EnrichedDayKernel.gen_balanced d.tensorEnrichedFunctor (E.inverse.obj X).X.toEnrichedFunctor
        (E.inverse.obj Y).X.toEnrichedFunctor k a a')

/-- The already-adopted whole projection HEq keeps both entire functions and the actual Iso. -/
def ProjectionHEqFormula (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (comparison : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.IsoFamily E tensor) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI := ModuleMappingR.moduleMonoidal d b S L B
  letI := tensor
  HEq (originalProjection d b S L B E tensor comparison)
    (fun (X Y : D) => RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
      (E.inverse.obj X) (E.inverse.obj Y) ≫ (comparison X Y).hom.hom)

/-- This is the same complete original quotient function, with no new heterogeneous obligation. -/
theorem projectionHEq_original (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (comparison : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.IsoFamily E tensor) :
    ProjectionHEqFormula d b S L B E tensor comparison := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let := ModuleMappingR.moduleMonoidal d b S L B
  let := tensor
  exact HEq.rfl

/-- The full original generator hypothesis tests every entire native tensor arrow. -/
def HomExtFamily (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (gamma : GeneratorFamily d S L E tensor) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  letI := tensor
  ∀ (X Y Z : D) (f g : X ⊗ Y ⟶ Z)
    (_h : ∀ (k : I) (a : I × I),
      gamma X Y k a ≫ EnrichedFunctorCat.component (E.inverse.map f).hom k =
        gamma X Y k a ≫ EnrichedFunctorCat.component (E.inverse.map g).hom k),
    f = g

/-- The exact original quotient and source equivalence make the whole generator test injective. -/
theorem homExtOriginal (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (comparison : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.IsoFamily E tensor) :
    HomExtFamily d S L E tensor (originalGenerator d b S L B E tensor comparison) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  let : ∀ U : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft U) :=
    (Closed.smallTensorPreservationFamilies d b).1
  let : ∀ U : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight U) :=
    (Closed.smallTensorPreservationFamilies d b).2
  let := ModuleMappingR.moduleMonoidal d b S L B
  let := tensor
  intro X Y Z f g h
  apply E.inverse.map_injective
  apply (cancel_epi (comparison X Y).hom).mp
  apply Mod.hom_ext
  let : Epi (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
    (E.inverse.obj X) (E.inverse.obj Y)) :=
      RightModuleFree.relativeTensorπ_epi (⟨S⟩ : EnrichedFunctorCat V I)
        (E.inverse.obj X) (E.inverse.obj Y)
  apply (cancel_epi (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
    (E.inverse.obj X) (E.inverse.obj Y))).mp
  apply EnrichedFunctorCat.hom_ext
  intro k
  rw [Mod.comp_hom', Mod.comp_hom', EnrichedFunctorCat.component_comp,
    EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp,
    EnrichedFunctorCat.component_comp]
  apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor
    (E.inverse.obj X).X.toEnrichedFunctor (E.inverse.obj Y).X.toEnrichedFunctor k
  intro a
  simpa only [originalGenerator,
    Coend.coendGenerator_formula,
    EnrichedFunctorCat.component_comp,
    Category.assoc] using h k a

/-- Compose the two original complete homogeneous squares without changing either map. -/
theorem originalComposeSquare {C : Type _} [Category C] {A A' B B' Q R : C}
    (p : A ⟶ B) (u : B ⟶ Q) (v : Q ⟶ R) (t : B ⟶ B')
    (s : A ⟶ A') (p' : A' ⟶ B') (u' : B' ⟶ R)
    (hu : t ≫ u' = u ≫ v) (hp : p ≫ t = s ≫ p') :
    (p ≫ u) ≫ v = s ≫ p' ≫ u' :=
  (Category.assoc p u v).trans
    ((congrArg (fun q => p ≫ q) hu.symm).trans
      ((Category.assoc p t u').symm.trans
        ((congrArg (fun q => q ≫ u') hp).trans (Category.assoc s p' u'))))

/-- The complete original source-projection Eq for every two original input maps. -/
def ProjectionNaturalFamily (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (comparison : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.IsoFamily E tensor) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  letI := ModuleMappingR.moduleMonoidal d b S L B
  letI := tensor
  ∀ {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y'),
    originalProjection d b S L B E tensor comparison X Y ≫ (E.inverse.map (f ⊗ₘ g)).hom =
      ((E.inverse.map f).hom ⊗ₘ (E.inverse.map g).hom) ≫
        originalProjection d b S L B E tensor comparison X' Y'

/-- Existing whole source tensorator naturality and the original quotient map square prove Eq. -/
theorem originalProjectionNatural (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (comparison : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.IsoFamily E tensor)
    (hNatural : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.Natural E tensor comparison) :
    ProjectionNaturalFamily d b S L B E tensor comparison := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let := ModuleMappingR.moduleMonoidal d b S L B
  let := tensor
  intro X X' Y Y' f g
  have hu := congrArg Mod.Hom.hom (hNatural f g)
  rw [Mod.comp_hom', Mod.comp_hom'] at hu
  have hp := RightModuleFree.relativeTensorMap_π (⟨S⟩ : EnrichedFunctorCat V I)
    (E.inverse.map f) (E.inverse.map g)
  exact originalComposeSquare
    (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
      (E.inverse.obj X) (E.inverse.obj Y))
    (comparison X Y).hom.hom (E.inverse.map (f ⊗ₘ g)).hom
    (E.inverse.map f ⊗ₘ E.inverse.map g).hom ((E.inverse.map f).hom ⊗ₘ (E.inverse.map g).hom)
    (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
      (E.inverse.obj X') (E.inverse.obj Y'))
    (comparison X' Y').hom.hom hu hp

/-- The complete original weighted generator Eq, keeping every coefficient and both source maps. -/
def GeneratorNaturalFamily (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (comparison : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.IsoFamily E tensor) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  letI := ModuleMappingR.moduleMonoidal d b S L B
  letI := tensor
  ∀ {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') (k : I) (a : I × I),
    originalGenerator d b S L B E tensor comparison X Y k a ≫
        EnrichedFunctorCat.component (E.inverse.map (f ⊗ₘ g)).hom k =
      (𝟙 (d.tensorEnrichedFunctor.obj a ⟶[V] k) ⊗ₘ
        (EnrichedFunctorCat.component (E.inverse.map f).hom a.1 ⊗ₘ
          EnrichedFunctorCat.component (E.inverse.map g).hom a.2)) ≫
        originalGenerator d b S L B E tensor comparison X' Y' k a

/-- The original full coend map square composes with the same original natural tensorator. -/
theorem originalGeneratorNatural (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (comparison : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.IsoFamily E tensor)
    (hNatural : letI := ModuleMappingR.moduleMonoidal d b S L B
      SourceTensorIso.Natural E tensor comparison) :
    GeneratorNaturalFamily d b S L B E tensor comparison := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let := ModuleMappingR.moduleMonoidal d b S L B
  let := tensor
  intro X X' Y Y' f g k a
  have hu := congrArg (fun q => EnrichedFunctorCat.component q.hom k) (hNatural f g)
  rw [Mod.comp_hom', Mod.comp_hom', EnrichedFunctorCat.component_comp,
    EnrichedFunctorCat.component_comp] at hu
  have hp := Coend.coendGenerator_map
    d b S L B (E.inverse.map f) (E.inverse.map g) k a
  exact originalComposeSquare
    (Coend.coendGenerator
      d b S L B (E.inverse.obj X) (E.inverse.obj Y) k a)
    (EnrichedFunctorCat.component (comparison X Y).hom.hom k)
    (EnrichedFunctorCat.component (E.inverse.map (f ⊗ₘ g)).hom k)
    (EnrichedFunctorCat.component (E.inverse.map f ⊗ₘ E.inverse.map g).hom k)
    (𝟙 (d.tensorEnrichedFunctor.obj a ⟶[V] k) ⊗ₘ
      (EnrichedFunctorCat.component (E.inverse.map f).hom a.1 ⊗ₘ
        EnrichedFunctorCat.component (E.inverse.map g).hom a.2))
    (Coend.coendGenerator
      d b S L B (E.inverse.obj X') (E.inverse.obj Y') k a)
    (EnrichedFunctorCat.component (comparison X' Y').hom.hom k) hu hp


/-- The full projection statement at the original comparison computed from the actual tensor Eq. -/
def ClosedProjectionNaturalFamily (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (hEq : letI := ModuleMappingR.moduleMonoidal d b S L B
      tensor = Monoidal.transport E) : Prop :=
  letI := ModuleMappingR.moduleMonoidal d b S L B
  ProjectionNaturalFamily d b S L B E tensor
    (SourceTensorIso.isoOfEq E tensor hEq)

/-- Close the entire original tensorator naturality proof before native data specialization. -/
theorem closedProjectionNatural (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (hEq : letI := ModuleMappingR.moduleMonoidal d b S L B
      tensor = Monoidal.transport E) : ClosedProjectionNaturalFamily d b S L B E tensor hEq := by
  let := ModuleMappingR.moduleMonoidal d b S L B
  intro X X' Y Y' f g
  exact originalProjectionNatural d b S L B E tensor
    (SourceTensorIso.isoOfEq E tensor hEq)
    (fun {X X' Y Y'} f g => SourceTensorIso.natural_of_eq E tensor hEq f g)
    f g

/-- The full weighted-generator statement at the same original computed source Iso. -/
def ClosedGeneratorNaturalFamily (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (hEq : letI := ModuleMappingR.moduleMonoidal d b S L B
      tensor = Monoidal.transport E) : Prop :=
  letI := ModuleMappingR.moduleMonoidal d b S L B
  GeneratorNaturalFamily d b S L B E tensor
    (SourceTensorIso.isoOfEq E tensor hEq)

/-- The original source tensorator proof is applied entirely in the generic source context. -/
@[reassoc]
theorem closedGeneratorNatural (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (hEq : letI := ModuleMappingR.moduleMonoidal d b S L B
      tensor = Monoidal.transport E) : ClosedGeneratorNaturalFamily d b S L B E tensor hEq := by
  let := ModuleMappingR.moduleMonoidal d b S L B
  intro X X' Y Y' f g k a
  exact originalGeneratorNatural d b S L B E tensor
    (SourceTensorIso.isoOfEq E tensor hEq)
    (fun {X X' Y Y'} f g => SourceTensorIso.natural_of_eq E tensor hEq f g)
    f g k a

end Quotient



namespace Braiding
universe uV vV uI vI uD vD
open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.Enriched CategoryTheory.EnrichedDayKernel
attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (B : EnrichedFunctor.LaxBraidedData L)
  {D : Type uD} [Category.{vD} D]

/-- The entire original target tensor is computed from the exact source module tensor. -/
@[instance_reducible]
def sourceTransport (E : ModuleMappingR.Module d S L ≌ D) : MonoidalCategory D :=
  letI := ModuleMappingR.moduleMonoidal d b S L B
  Monoidal.transport E

/-- The actual computed target symmetry uses the original source symmetry and tensor equality. -/
def targetSymmetry (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (h : tensor = sourceTransport d b S L B E) : Monoidal.Transport.SymmetricType tensor :=
  letI := ModuleMappingR.moduleMonoidal d b S L B
  letI := ModuleMappingR.moduleSymmetric d b S L B
  Monoidal.Transport.moveSymmetric tensor (Monoidal.transport E) h
    (Monoidal.Transport.sourceSymmetric E)

/-- The complete original source-Iso braid property, with all original module/native maps. -/
def TensorIsoFormula (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (h : tensor = sourceTransport d b S L B E) : Prop :=
  letI := ModuleMappingR.moduleMonoidal d b S L B
  letI := ModuleMappingR.moduleSymmetric d b S L B
  SourceTensorIso.Braiding E tensor h

/--
The entire original source-Iso braid equation follows from its original unit, without a premise.
-/
@[reassoc]
theorem tensorIso_source (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (h : tensor = sourceTransport d b S L B E) : TensorIsoFormula d b S L B E tensor h := by
  let := ModuleMappingR.moduleMonoidal d b S L B
  let := ModuleMappingR.moduleSymmetric d b S L B
  exact SourceTensorIso.braiding_of_eq E tensor h

/--
The complete ambient Day projection braid preserves the entire original comparison carrier maps.
-/
def ProjectionFormula (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (h : tensor = sourceTransport d b S L B E) : Prop :=
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
    letI : ∀ X : EnrichedFunctorCat V I,
        PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
      (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).1
    letI : ∀ X : EnrichedFunctorCat V I,
        PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
      (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).2
    letI := ModuleMappingR.moduleMonoidal d b S L B
    letI := ModuleMappingR.moduleSymmetric d b S L B
    letI := tensor
    letI : SymmetricCategory D := targetSymmetry d b S L B E tensor h
    ∀ (X Y : D),
      Quotient.originalProjection d b S L B E tensor
          (SourceTensorIso.isoOfEq E tensor h) X Y ≫
        (E.inverse.map (β_ X Y).hom).hom =
      (β_ (E.inverse.obj X).X (E.inverse.obj Y).X).hom ≫
        Quotient.originalProjection d b S L B E tensor
          (SourceTensorIso.isoOfEq E tensor h) Y X

/--
The original quotient braid followed by the original source-unit braid gives the full ambient
Eq.
-/
@[reassoc]
theorem projection_source (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (h : tensor = sourceTransport d b S L B E) : ProjectionFormula d b S L B E tensor h := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).1
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).2
  let := ModuleMappingR.moduleMonoidal d b S L B
  let := ModuleMappingR.moduleSymmetric d b S L B
  let := tensor
  let : SymmetricCategory D := targetSymmetry d b S L B E tensor h
  intro X Y
  let comparison : ∀ (X Y : D), E.inverse.obj X ⊗ E.inverse.obj Y ≅ E.inverse.obj (X ⊗ Y) :=
    SourceTensorIso.isoOfEq E tensor h
  have hi := SourceTensorIso.braiding_of_eq E tensor h X Y
  have hc := congrArg (fun q => q.hom) hi
  rw [Mod.comp_hom', Mod.comp_hom'] at hc
  have hp := RightModuleFree.relativeTensorBraiding_hom_π
    (⟨S⟩ : EnrichedFunctorCat V I) (E.inverse.obj X) (E.inverse.obj Y)
  have hpSource : RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
      (E.inverse.obj X) (E.inverse.obj Y) ≫
      (β_ (E.inverse.obj X) (E.inverse.obj Y)).hom.hom =
      (β_ (E.inverse.obj X).X (E.inverse.obj Y).X).hom ≫
        RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
          (E.inverse.obj Y) (E.inverse.obj X) := hp
  change (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
      (E.inverse.obj X) (E.inverse.obj Y) ≫
      (comparison X Y).hom.hom) ≫ (E.inverse.map (β_ X Y).hom).hom = _
  calc
    _ = RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
      (E.inverse.obj X) (E.inverse.obj Y) ≫
        ((comparison X Y).hom.hom ≫ (E.inverse.map (β_ X Y).hom).hom) := Category.assoc _ _ _
    _ = RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
      (E.inverse.obj X) (E.inverse.obj Y) ≫
        ((β_ (E.inverse.obj X) (E.inverse.obj Y)).hom.hom ≫ (comparison Y X).hom.hom) := by rw [hc]
    _ = (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
      (E.inverse.obj X) (E.inverse.obj Y) ≫
        (β_ (E.inverse.obj X) (E.inverse.obj Y)).hom.hom) ≫ (comparison Y X).hom.hom :=
      (Category.assoc _ _ _).symm
    _ = ((β_ (E.inverse.obj X).X (E.inverse.obj Y).X).hom ≫
        RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
          (E.inverse.obj Y) (E.inverse.obj X)) ≫
          (comparison Y X).hom.hom := congrArg (fun q => q ≫ (comparison Y X).hom.hom) hpSource
    _ = _ := Category.assoc _ _ _

/-- The whole original projection braid, retaining arbitrary ambient postcomposition. -/
def ProjectionAssocFormula (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D)
    (h : tensor = sourceTransport d b S L B E) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).1
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).2
  letI := ModuleMappingR.moduleMonoidal d b S L B
  letI := ModuleMappingR.moduleSymmetric d b S L B
  letI := tensor
  letI : SymmetricCategory D := targetSymmetry d b S L B E tensor h
  ∀ (X Y : D) {Z : EnrichedFunctorCat V I}
    (k : (E.inverse.obj (Y ⊗ X)).X ⟶ Z),
    Quotient.originalProjection d b S L B E tensor
        (SourceTensorIso.isoOfEq E tensor h) X Y ≫
      (E.inverse.map (β_ X Y).hom).hom ≫ k =
    (β_ (E.inverse.obj X).X (E.inverse.obj Y).X).hom ≫
      Quotient.originalProjection d b S L B E tensor
        (SourceTensorIso.isoOfEq E tensor h) Y X ≫ k

/-- The canonical supplier is closed at the independently written full original type. -/
theorem projectionAssoc_source (E : ModuleMappingR.Module d S L ≌ D)
    (tensor : MonoidalCategory D) (h : tensor = sourceTransport d b S L B E) :
    ProjectionAssocFormula d b S L B E tensor h := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).1
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).2
  let := ModuleMappingR.moduleMonoidal d b S L B
  let := ModuleMappingR.moduleSymmetric d b S L B
  let := tensor
  let : SymmetricCategory D := targetSymmetry d b S L B E tensor h
  intro X Y Z k
  exact (Category.assoc _ _ k).symm.trans
    ((congrArg (fun t => t ≫ k) (projection_source d b S L B E tensor h X Y)).trans
      (Category.assoc _ _ k))

end Braiding




end CategoryTheory.ModuleMappingRTransport
