/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereSmashScalars
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeTensor
public import MathlibExt.CategoryTheory.Monoidal.RightModuleRelativeTensorCoherence
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRAdjunctionBase
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRTransport
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ClosedColimits
public import MathlibExt.Topology.Category.PointedCGWH.EnrichedMappingEnds

/-!
# The actual continuous orthogonal sphere tensor

The original continuous Day adjunction supplies both entire tensor
preservation families. Native pointwise colimits supply the coequalizers.
The canonical stock right-sphere-module relative tensor is constructed
from those original source maps, with no tensor or model outcome assumed.

The named native structures reuse the canonical relative tensor directly.
Every original quotient map and complete source identity is retained.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.Internal

universe uV vV uI vI
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits

/-- Associating an existing composite equality preserves both independent input maps. -/
private theorem compThroughAssociator {C : Type uV} [Category.{vV} C]
    {A B D E F G : C} (inner : A ⟶ B) (outer : B ⟶ D)
    (p : D ⟶ E) (q : E ⟶ G) (r : D ⟶ F) (t : F ⟶ G)
    (h : p ≫ q = r ≫ t) :
    (inner ≫ outer ≫ p) ≫ q = inner ≫ outer ≫ r ≫ t :=
  (Category.assoc inner (outer ≫ p) q).trans
    ((congrArg (fun f => inner ≫ f) (Category.assoc outer p q)).trans
      (congrArg (fun f => inner ≫ outer ≫ f) h))

/-- Ordinary enriched components lift a complete three-map source equation. -/
private theorem componentThreeEquation
    {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
    [SymmetricCategory V] [MonoidalClosed V]
    {I : Type uI} [EnrichedCategory V I]
    {A B C D E F : EnrichedFunctorCat V I}
    (f : A ⟶ B) (g : B ⟶ C) (a : C ⟶ D)
    (r : A ⟶ E) (t : E ⟶ F) (u : F ⟶ D)
    (h : f ≫ g ≫ a = r ≫ t ≫ u) (k : I) :
    EnrichedFunctorCat.component (f ≫ g) k ≫ EnrichedFunctorCat.component a k =
      EnrichedFunctorCat.component r k ≫ EnrichedFunctorCat.component (t ≫ u) k := by
  have hSource := (Category.assoc f g a).trans h
  have hComponent := congrArg (fun q => EnrichedFunctorCat.component q k) hSource
  exact ((EnrichedFunctorCat.component_comp (f ≫ g) a k).symm.trans hComponent).trans
    (EnrichedFunctorCat.component_comp r (t ≫ u) k)

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
      (⟨S⟩ : EnrichedFunctorCat V I)) := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ (X Y : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (k : I) (a : I × I),
      EnrichedDayKernel.objects d.tensorEnrichedFunctor
          X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a ⟶
        (X ⊗ Y).X.toEnrichedFunctor.obj k := by
  exact ModuleMappingRTransport.Coend.coendGenerator d b S L B

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
      (⟨S⟩ : EnrichedFunctorCat V I)) := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ {X X' Y Y' : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I)}
      (f : X ⟶ X') (g : Y ⟶ Y') (k : I) (a : I × I),
      coendGenerator d b S L B X Y k a ≫
          EnrichedFunctorCat.component (f ⊗ₘ g).hom k =
        (𝟙 (d.tensorEnrichedFunctor.obj a ⟶[V] k) ⊗ₘ
          (EnrichedFunctorCat.component f.hom a.1 ⊗ₘ
            EnrichedFunctorCat.component g.hom a.2)) ≫
          coendGenerator d b S L B X' Y' k a := by
  exact ModuleMappingRTransport.Coend.coendGenerator_map d b S L B

include b B in
/-- The original source braid acts on the full coefficient by its inverse index isometry. -/
theorem coendGenerator_braiding :
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
      (⟨S⟩ : EnrichedFunctorCat V I)) := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    letI := RightModuleFree.tensorSymmetric (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ (X Y : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (k : I) (a : I × I),
      coendGenerator d b S L B X Y k a ≫
          EnrichedFunctorCat.component (β_ X Y).hom.hom k =
        (eHomWhiskerRight V (β_ a.1 a.2).inv k ⊗ₘ
          (β_ (X.X.toEnrichedFunctor.obj a.1) (Y.X.toEnrichedFunctor.obj a.2)).hom) ≫
          coendGenerator d b S L B Y X k (a.2, a.1) := by
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
    (⟨S⟩ : EnrichedFunctorCat V I)) := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  let := RightModuleFree.tensorSymmetric (⟨S⟩ : EnrichedFunctorCat V I)
  intro X Y k a
  have h := congrArg (fun q => EnrichedFunctorCat.component q k)
    (RightModuleFree.relativeTensorBraiding_hom_π (⟨S⟩ : EnrichedFunctorCat V I) X Y)
  rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp] at h
  have hb := EnrichedDayKernel.BraidingMonoidal.braiding_hom_component d b X.X Y.X k
  have hg := EnrichedDayKernel.BraidingComponents.gen_component d b
    X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a
  let sourceGen := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a
  have hg' := (congrArg (fun q => sourceGen ≫ q) hb).trans hg
  have h' := congrArg (fun q => sourceGen ≫ q) h
  have ha := Category.assoc sourceGen (EnrichedFunctorCat.component (β_ X.X Y.X).hom k)
    (EnrichedFunctorCat.component (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) Y X) k)
  have h'' := h'.trans (ha.symm.trans
    (congrArg (fun q => q ≫
      EnrichedFunctorCat.component (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) Y X) k) hg'))
  have ha' := Category.assoc
    (eHomWhiskerRight V (β_ a.1 a.2).inv k ⊗ₘ
      (β_ (X.X.toEnrichedFunctor.obj a.1) (Y.X.toEnrichedFunctor.obj a.2)).hom)
    (EnrichedDayKernel.gen d.tensorEnrichedFunctor Y.X.toEnrichedFunctor
      X.X.toEnrichedFunctor k (a.2, a.1))
    (EnrichedFunctorCat.component (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) Y X) k)
  have ha₀ := Category.assoc sourceGen
    (EnrichedFunctorCat.component (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) X Y) k)
    (EnrichedFunctorCat.component (β_ X Y).hom.hom k)
  simpa only [sourceGen, coendGenerator,
    ModuleMappingRTransport.Coend.coendGenerator_formula] using ha₀.trans (h''.trans ha')

include b B in
/-- Both independent coend coefficients and both original quotient maps are retained. -/
def leftNestedCoendGenerator :
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
      (⟨S⟩ : EnrichedFunctorCat V I)) := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ (X Y Z : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (k m n : I) (a : I × I),
      (d.tensorEnrichedFunctor.obj (m, n) ⟶[V] k) ⊗
          (EnrichedDayKernel.objects d.tensorEnrichedFunctor
            X.X.toEnrichedFunctor Y.X.toEnrichedFunctor m a ⊗ Z.X.toEnrichedFunctor.obj n) ⟶
        ((X ⊗ Y) ⊗ Z).X.toEnrichedFunctor.obj k := by
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
    (⟨S⟩ : EnrichedFunctorCat V I)) := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  intro X Y Z k m n a
  exact ((d.tensorEnrichedFunctor.obj (m, n) ⟶[V] k) ◁
      (EnrichedDayKernel.gen d.tensorEnrichedFunctor X.X.toEnrichedFunctor
        Y.X.toEnrichedFunctor m a ▷ Z.X.toEnrichedFunctor.obj n)) ≫
    EnrichedDayKernel.gen d.tensorEnrichedFunctor
      (X.X ⊗ Y.X).toEnrichedFunctor Z.X.toEnrichedFunctor k (m, n) ≫
        EnrichedFunctorCat.component
          ((RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) X Y ▷ Z.X) ≫
            RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) (X ⊗ Y) Z) k

/-- The primitive relative tensor preserves both entire nested source coefficients. -/
private theorem primitiveExpandedChain :
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
      (⟨S⟩ : EnrichedFunctorCat V I)) := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ (X Y Z : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (k m n : I) (a : I × I),
      (((d.tensorEnrichedFunctor.obj (m, n) ⟶[V] k) ◁
          (EnrichedDayKernel.gen d.tensorEnrichedFunctor X.X.toEnrichedFunctor
            Y.X.toEnrichedFunctor m a ▷ Z.X.toEnrichedFunctor.obj n)) ≫
        EnrichedDayKernel.gen d.tensorEnrichedFunctor
          (X.X ⊗ Y.X).toEnrichedFunctor Z.X.toEnrichedFunctor k (m, n) ≫
          EnrichedFunctorCat.component
            ((RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) X Y ▷ Z.X) ≫
              RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) (X ⊗ Y) Z) k) ≫
          EnrichedFunctorCat.component (α_ X Y Z).hom.hom k =
        ((d.tensorEnrichedFunctor.obj (m, n) ⟶[V] k) ◁
          (EnrichedDayKernel.gen d.tensorEnrichedFunctor X.X.toEnrichedFunctor
            Y.X.toEnrichedFunctor m a ▷ Z.X.toEnrichedFunctor.obj n)) ≫
          EnrichedDayKernel.gen d.tensorEnrichedFunctor
            (X.X ⊗ Y.X).toEnrichedFunctor Z.X.toEnrichedFunctor k (m, n) ≫
            EnrichedFunctorCat.component (α_ X.X Y.X Z.X).hom k ≫
              EnrichedFunctorCat.component
                ((X.X ◁ RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) Y Z) ≫
                  RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) X (Y ⊗ Z)) k := by
  intro dayMonoidal daySymmetric scalarMonoid scalarComm nativeCoequalizers
    tensorLeftPres tensorRightPres moduleMonoidal X Y Z k m n a
  let inner := ((d.tensorEnrichedFunctor.obj (m, n) ⟶[V] k) ◁
    (EnrichedDayKernel.gen d.tensorEnrichedFunctor X.X.toEnrichedFunctor
      Y.X.toEnrichedFunctor m a ▷ Z.X.toEnrichedFunctor.obj n))
  let outer := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    (X.X ⊗ Y.X).toEnrichedFunctor Z.X.toEnrichedFunctor k (m, n)
  let p := EnrichedFunctorCat.component
    ((RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) X Y ▷ Z.X) ≫
      RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) (X ⊗ Y) Z) k
  let q := EnrichedFunctorCat.component (α_ X Y Z).hom.hom k
  let r := EnrichedFunctorCat.component (α_ X.X Y.X Z.X).hom k
  let t := EnrichedFunctorCat.component
    ((X.X ◁ RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) Y Z) ≫
      RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) X (Y ⊗ Z)) k
  have h : p ≫ q = r ≫ t :=
    componentThreeEquation
      (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) X Y ▷ Z.X)
      (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) (X ⊗ Y) Z)
      (α_ X Y Z).hom.hom
      (α_ X.X Y.X Z.X).hom
      (X.X ◁ RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) Y Z)
      (RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) X (Y ⊗ Z))
      (RightModuleFree.relativeTensorAssociator_hom_π (⟨S⟩ : EnrichedFunctorCat V I) X Y Z) k
  exact compThroughAssociator inner outer p q r t h


/-- The full source associator equation for the nested continuous Day generator. -/
abbrev leftNestedCoendGeneratorAssociatorType : Prop :=
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
      (⟨S⟩ : EnrichedFunctorCat V I)) := Enriched.ModuleMappingR.moduleMonoidal d b S L B
    ∀ (X Y Z : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (k m n : I) (a : I × I),
      leftNestedCoendGenerator d b S L B X Y Z k m n a ≫
          EnrichedFunctorCat.component (α_ X Y Z).hom.hom k =
        ((d.tensorEnrichedFunctor.obj (m, n) ⟶[V] k) ◁
          (EnrichedDayKernel.gen d.tensorEnrichedFunctor X.X.toEnrichedFunctor
            Y.X.toEnrichedFunctor m a ▷ Z.X.toEnrichedFunctor.obj n)) ≫
          EnrichedDayKernel.gen d.tensorEnrichedFunctor
            (X.X ⊗ Y.X).toEnrichedFunctor Z.X.toEnrichedFunctor k (m, n) ≫
            EnrichedFunctorCat.component (α_ X.X Y.X Z.X).hom k ≫
              EnrichedFunctorCat.component
                ((X.X ◁ RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) Y Z) ≫
                  RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I) X (Y ⊗ Z)) k

/-- The source associator conserves every inner and outer coefficient through the
original Day map. -/
theorem leftNestedCoendGenerator_associator :
    leftNestedCoendGeneratorAssociatorType d b S L B :=
  primitiveExpandedChain d b S L B

end CoendMaps

end PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.Internal

namespace PointedCGWH.Spectra.Orthogonal.SphereSmashStructure

/-- The continuous isometry category used by the original orthogonal source. -/
local instance indexCategory : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original direct sum tensor on the continuous orthogonal index. -/
local instance indexMonoidalCategory : MonoidalCategory OrthogonalIndex :=
  OrthogonalIndex.monoidalCategory.{u, v}
/-- The pointed continuous enrichment of the original orthogonal index. -/
local instance indexEnrichedOrdinaryCategory :
    EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block symmetry of the continuous orthogonal index. -/
local instance indexSymmetricCategory : SymmetricCategory OrthogonalIndex :=
  OrthogonalIndex.symmetricCategory.{u, v}
attribute [local instance] Enriched.prodCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits

/-- The unchanged genuine continuous orthogonal space category. -/
abbrev ISpace := EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex

/-- The continuous Day tensor on the original orthogonal spaces. -/
local instance dayMonoidalCategory : MonoidalCategory ISpace.{u, v} :=
  OrthogonalDay.monoidalCategory.{u, v}
/-- The original continuous Day symmetry on orthogonal spaces. -/
local instance daySymmetricCategory : SymmetricCategory ISpace.{u, v} :=
  OrthogonalDay.symmetricCategory.{u, v}
/-- The original representation sphere monoid for the continuous Day tensor. -/
local instance sphereMonoid : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}
local instance sphereCommutativeMonoid : IsCommMonObj sphereISpace.{u, v} :=
  OrthogonalDay.sphereIsCommMonObj.{u, v}
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}

/-- Actual native pointwise colimits provide all required I-space coequalizers. -/
theorem hasCoequalizers : HasCoequalizers ISpace.{u, v} := by infer_instance

local instance spaceCoequalizers : HasCoequalizers ISpace.{u, v} := hasCoequalizers.{u, v}

/-- The original closed Day structure on all continuous orthogonal coefficient diagrams. -/
local instance nativeDayClosed : MonoidalClosed ISpace.{u, v} :=
  EnrichedDayKernel.Closed.monoidalClosed OrthogonalIndex.enrichedMonoidalData.{u, v}
private instance nativeTensorLeftPreserves :
    ∀ X : ISpace.{u, v}, PreservesColimitsOfSize.{0, 0} (tensorLeft X) := fun _ => inferInstance
private instance nativeTensorRightPreserves :
    ∀ X : ISpace.{u, v}, PreservesColimitsOfSize.{0, 0} (tensorRight X) := fun _ => inferInstance

/-- The actual stock right-module monoidal structure, with all original relative tensor maps. -/
@[instance_reducible]
def monoidalCategory : MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  Enriched.ModuleMappingR.moduleMonoidal OrthogonalIndex.enrichedMonoidalData.{u, v}
    OrthogonalIndex.enrichedSymmetricData.{u, v} orthogonalSphereFunctor.{u, v}
    orthogonalSphereMonoidalData.{u, v} orthogonalSphereBraidedData.{u, v}

/-- The canonical relative tensor on the same original native sphere modules. -/
local instance : MonoidalCategory NativeSphereModule.Carrier.{u, v} := monoidalCategory.{u, v}

/-- The actual stock right-module symmetry from the same canonical relative tensor. -/
@[instance_reducible]
def symmetricCategory : SymmetricCategory NativeSphereModule.Carrier.{u, v} :=
  Enriched.ModuleMappingR.moduleSymmetric OrthogonalIndex.enrichedMonoidalData.{u, v}
    OrthogonalIndex.enrichedSymmetricData.{u, v} orthogonalSphereFunctor.{u, v}
    orthogonalSphereMonoidalData.{u, v} orthogonalSphereBraidedData.{u, v}

end PointedCGWH.Spectra.Orthogonal.SphereSmashStructure
