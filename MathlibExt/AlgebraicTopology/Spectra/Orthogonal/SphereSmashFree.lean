/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.RightModuleFreeEvaluation
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereSmashCoherence
import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.FreePairComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceRightModuleFreeEvaluation

/-!
# Actual free orthogonal sphere smash

The original two-free relative tensorator first multiplies the complete
sphere factors. The genuine enriched Day free-pair comparison then contracts
the two original I-space free coefficients. Both module maps retain the
original right sphere action, all continuous isometry coefficients and the
original coequalizer projection. No free-smash formula is a caller input.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.Spectra CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Primitive

universe uC vC
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The literal complete two-free Iso on the selected original right-module tensor. -/
def PairIsoType (P Q R : C) :=
  letI := RightModuleFree.tensorMonoidal M
  RightModuleFree.freeObject M P ⊗ RightModuleFree.freeObject M Q ≅
    RightModuleFree.freeObject M R

/-- Apply the original stock free functor to an actual base comparison after its tensorator. -/
def ofIso (P Q R : C) (e : P ⊗ Q ≅ R) : PairIsoType M P Q R := by
  letI := RightModuleFree.tensorMonoidal M
  exact RightModuleFree.freeTensorIso M P Q ≪≫ (RightModuleFree.functor M).mapIso e

/-- The literal compatibility equation for both original base maps and the original target map. -/
def Compatible {P P' Q Q' R R' : C}
    (f : P ⟶ P') (g : Q ⟶ Q') (r : R ⟶ R')
    (e : P ⊗ Q ≅ R) (e' : P' ⊗ Q' ≅ R') : Prop :=
  (f ⊗ₘ g) ≫ e'.hom = e.hom ≫ r

/-- The full original two-free naturality equation, on the same selected relative tensor. -/
def NaturalityProperty {P P' Q Q' R R' : C}
    (f : P ⟶ P') (g : Q ⟶ Q') (r : R ⟶ R')
    (e : P ⊗ Q ≅ R) (e' : P' ⊗ Q' ≅ R') : Prop :=
  letI := RightModuleFree.tensorMonoidal M
  (RightModuleFree.freeMap M f ⊗ₘ RightModuleFree.freeMap M g) ≫
      (ofIso M P' Q' R' e').hom =
    (ofIso M P Q R e).hom ≫ RightModuleFree.freeMap M r

/-- The entire carrier map contains the original tensorator and original right-free map. -/
theorem ofIso_hom (P Q R : C) (e : P ⊗ Q ≅ R) :
    letI := RightModuleFree.tensorMonoidal M
    (ofIso M P Q R e).hom.hom = (RightModuleFree.freeTensorIso M P Q).hom.hom ≫ (e.hom ▷ M) := by
  let := RightModuleFree.tensorMonoidal M
  rfl

/-- The literal entire original composed two-free projection equation. -/
def OfIsoProjectionFormula (P Q R : C) (e : P ⊗ Q ≅ R) : Prop :=
  letI := RightModuleFree.tensorMonoidal M
  RightModuleFree.relativeTensorπ M (RightModuleFree.freeObject M P)
      (RightModuleFree.freeObject M Q) ≫ (ofIso M P Q R e).hom.hom =
    tensorμ P M Q M ≫ ((P ⊗ Q) ◁ MonObj.mul (X := M)) ≫ (e.hom ▷ M)

/-- Every whole prequotient coefficient is multiplied by the original complete monoid map. -/
theorem ofIso_projection (P Q R : C) (e : P ⊗ Q ≅ R) :
    OfIsoProjectionFormula M P Q R e := by
  let := RightModuleFree.tensorMonoidal M
  have h := RightModuleFree.freeTensorIso_hom_π M P Q
  change RightModuleFree.relativeTensorπ M _ _ ≫
    ((RightModuleFree.freeTensorIso M P Q).hom.hom ≫ (e.hom ▷ M)) = _
  simpa only [Category.assoc] using congrArg (fun f => f ≫ (e.hom ▷ M)) h

/-- The literal entire original composed inverse, with its original generator and quotient. -/
def OfIsoInverseFormula (P Q R : C) (e : P ⊗ Q ≅ R) : Prop :=
  letI := RightModuleFree.tensorMonoidal M
  (ofIso M P Q R e).inv.hom =
    (e.inv ▷ M) ≫ (α_ P Q M).hom ≫
      (RightModuleFree.freeGenerator M P ▷ (Q ⊗ M)) ≫
        RightModuleFree.relativeTensorπ M (RightModuleFree.freeObject M P)
          (RightModuleFree.freeObject M Q)

/-- The entire inverse retains the original unit insertion and original sphere quotient. -/
theorem ofIso_inv (P Q R : C) (e : P ⊗ Q ≅ R) :
    OfIsoInverseFormula M P Q R e := by
  let := RightModuleFree.tensorMonoidal M
  have h := RightModuleFree.freeTensorIso_inv M P Q
  change (e.inv ▷ M) ≫ (RightModuleFree.freeTensorIso M P Q).inv.hom = _
  exact congrArg (fun f => (e.inv ▷ M) ≫ f) h

/-- Both complete source maps and the complete target map preserve the actual free comparison. -/
theorem ofIso_naturality {P P' Q Q' R R' : C}
    (f : P ⟶ P') (g : Q ⟶ Q') (r : R ⟶ R')
    (e : P ⊗ Q ≅ R) (e' : P' ⊗ Q' ≅ R')
    (he : (f ⊗ₘ g) ≫ e'.hom = e.hom ≫ r) :
    letI := RightModuleFree.tensorMonoidal M
    (RightModuleFree.freeMap M f ⊗ₘ RightModuleFree.freeMap M g) ≫
        (ofIso M P' Q' R' e').hom =
      (ofIso M P Q R e).hom ≫ RightModuleFree.freeMap M r := by
  let := RightModuleFree.tensorMonoidal M
  have hf := RightModuleFree.freeTensorIso_naturality M f g
  have h1 := (RightModuleFree.functor M).map_comp (f ⊗ₘ g) e'.hom
  have h2 := (RightModuleFree.functor M).map_comp e.hom r
  have hm : RightModuleFree.freeMap M (f ⊗ₘ g) ≫ RightModuleFree.freeMap M e'.hom =
      RightModuleFree.freeMap M e.hom ≫ RightModuleFree.freeMap M r :=
    h1.symm.trans ((congrArg (fun h => (RightModuleFree.functor M).map h) he).trans h2)
  change (RightModuleFree.freeMap M f ⊗ₘ RightModuleFree.freeMap M g) ≫
      ((RightModuleFree.freeTensorIso M P' Q').hom ≫ RightModuleFree.freeMap M e'.hom) =
    ((RightModuleFree.freeTensorIso M P Q).hom ≫ RightModuleFree.freeMap M e.hom) ≫
      RightModuleFree.freeMap M r
  calc
    _ = ((RightModuleFree.freeMap M f ⊗ₘ RightModuleFree.freeMap M g) ≫
        (RightModuleFree.freeTensorIso M P' Q').hom) ≫ RightModuleFree.freeMap M e'.hom :=
      (Category.assoc _ _ _).symm
    _ = ((RightModuleFree.freeTensorIso M P Q).hom ≫ RightModuleFree.freeMap M (f ⊗ₘ g)) ≫
        RightModuleFree.freeMap M e'.hom := congrArg (fun h => h ≫ _) hf
    _ = (RightModuleFree.freeTensorIso M P Q).hom ≫
        (RightModuleFree.freeMap M (f ⊗ₘ g) ≫ RightModuleFree.freeMap M e'.hom) :=
      Category.assoc _ _ _
    _ = (RightModuleFree.freeTensorIso M P Q).hom ≫
        (RightModuleFree.freeMap M e.hom ≫ RightModuleFree.freeMap M r) :=
      congrArg (fun h => (RightModuleFree.freeTensorIso M P Q).hom ≫ h) hm
    _ = _ := (Category.assoc _ _ _).symm

/-- Original proved base compatibility supplies the complete original module naturality. -/
theorem naturality_spec {P P' Q Q' R R' : C}
    (f : P ⟶ P') (g : Q ⟶ Q') (r : R ⟶ R')
    (e : P ⊗ Q ≅ R) (e' : P' ⊗ Q' ≅ R')
    (he : Compatible f g r e e') : NaturalityProperty M f g r e e' :=
  ofIso_naturality M f g r e e' he

end PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Primitive

namespace PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Evaluation

universe uV vV uI
open EnrichedFunctorCat
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)] [SymmetricCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The literal free/evaluation source objects in the original selected right tensor. -/
def PairIsoType (n m r : I) (X Y : V) :=
  letI := RightModuleFree.tensorMonoidal S
  (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj X ⊗
      (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S m).obj Y ≅
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S r).obj (X ⊗ Y)

/-- The original free/evaluation composite uses the same actual free-module tensor maps. -/
def ofIso (n m r : I) (X Y : V)
    (e : Free.object n X ⊗ Free.object m Y ≅ Free.object r (X ⊗ Y)) :
    PairIsoType S n m r X Y :=
  Primitive.ofIso S (Free.object n X) (Free.object m Y) (Free.object r (X ⊗ Y)) e

end PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Evaluation

namespace PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Internal

universe uV vV uI vI
open EnrichedFunctorCat
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

/-- The actual Day tensor of the two original free diagrams, with both original coefficients. -/
def diagramPair (n m : I) (X Y : V) :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    Free.object n X ⊗ Free.object m Y ≅ Free.object (n ⊗ m) (X ⊗ Y) := by
  letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
  exact EnrichedDayKernel.FreePairComparison.iso d.tensorEnrichedFunctor n m X Y

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- The true Day pair preserves both full coefficient arrows in the original ambient tensor. -/
theorem diagramPair_coefficient (n m : I) {X X' Y Y' : V}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    (Free.coefficientMap n f ⊗ₘ Free.coefficientMap m g) ≫
        (diagramPair d n m X' Y').hom =
      (diagramPair d n m X Y).hom ≫ Free.coefficientMap (n ⊗ m) (f ⊗ₘ g) := by
  let := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
  have ht := EnrichedDayKernel.ColimitMonoidal.tensorHom_eq d
    (Free.coefficientMap n f) (Free.coefficientMap m g)
  have hn := EnrichedDayKernel.FreePairComparison.iso_coefficient d.tensorEnrichedFunctor n m f g
  exact (congrArg (fun h => h ≫ (diagramPair d n m X' Y').hom) ht).trans hn

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Both complete original contravariant source points preserve the genuine ambient Day pair. -/
theorem diagramPair_source {n n' m m' : I}
    (p : 𝟙_ V ⟶ (n ⟶[V] n')) (q : 𝟙_ V ⟶ (m ⟶[V] m')) (X Y : V) :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    (Free.sourceMap p X ⊗ₘ Free.sourceMap q Y) ≫ (diagramPair d n m X Y).hom =
      (diagramPair d n' m' X Y).hom ≫
        Free.sourceMap (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ≫
          d.tensorEnrichedFunctor.map (n, m) (n', m')) (X ⊗ Y) := by
  let := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
  have ht := EnrichedDayKernel.ColimitMonoidal.tensorHom_eq d
    (Free.sourceMap p X) (Free.sourceMap q Y)
  have hn := EnrichedDayKernel.FreePairComparison.iso_source d.tensorEnrichedFunctor p q X Y
  exact (congrArg (fun h => h ≫ (diagramPair d n m X Y).hom) ht).trans hn

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- The entire native coefficient compatibility retains its original full base equation. -/
theorem diagramPair_coefficient_spec (n m : I) {X X' Y Y' : V}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    Primitive.Compatible (Free.coefficientMap n f) (Free.coefficientMap m g)
      (Free.coefficientMap (n ⊗ m) (f ⊗ₘ g))
      (diagramPair d n m X Y) (diagramPair d n m X' Y') :=
  diagramPair_coefficient d n m f g

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Both entire native source arrows retain the complete original base compatibility equation. -/
theorem diagramPair_source_spec {n n' m m' : I}
    (p : 𝟙_ V ⟶ (n ⟶[V] n')) (q : 𝟙_ V ⟶ (m ⟶[V] m')) (X Y : V) :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    Primitive.Compatible (Free.sourceMap p X) (Free.sourceMap q Y)
      (Free.sourceMap (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ≫
        d.tensorEnrichedFunctor.map (n, m) (n', m')) (X ⊗ Y))
      (diagramPair d n' m' X Y) (diagramPair d n m X Y) :=
  diagramPair_source d p q X Y

/-- Construct the full free relative tensor comparison from the two original tensorators. -/
def pairFromDay
    (hLeft : letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
      ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X))
    (hRight : letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
      ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)) :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    letI := EnrichedDayKernel.BraidingMonoidal.symmetricCategory d b
    letI := EnrichedDayKernel.LaxMonoid.monObj d S L
    letI := EnrichedDayKernel.LaxMonoid.isCommMonObj d b S L B
    letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
    letI := hLeft
    letI := hRight
    letI := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ (n m : I) (X Y : V),
      RightModuleFree.freeObject (⟨S⟩ : EnrichedFunctorCat V I) (Free.object n X) ⊗
          RightModuleFree.freeObject (⟨S⟩ : EnrichedFunctorCat V I) (Free.object m Y) ≅
        RightModuleFree.freeObject (⟨S⟩ : EnrichedFunctorCat V I)
          (Free.object (n ⊗ m) (X ⊗ Y)) := by
  letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
  letI := EnrichedDayKernel.BraidingMonoidal.symmetricCategory d b
  letI := EnrichedDayKernel.LaxMonoid.monObj d S L
  letI := EnrichedDayKernel.LaxMonoid.isCommMonObj d b S L B
  letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  letI := hLeft
  letI := hRight
  letI := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  intro n m X Y
  exact RightModuleFree.freeTensorIso (⟨S⟩ : EnrichedFunctorCat V I)
      (Free.object n X) (Free.object m Y) ≪≫
    (RightModuleFree.functor (⟨S⟩ : EnrichedFunctorCat V I)).mapIso (diagramPair d n m X Y)

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- Before the sphere quotient, both complete sphere factors are multiplied by the original map. -/
theorem pairFromDay_projection
    (hLeft : letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
      ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X))
    (hRight : letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
      ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)) :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    letI := EnrichedDayKernel.BraidingMonoidal.symmetricCategory d b
    letI := EnrichedDayKernel.LaxMonoid.monObj d S L
    letI := EnrichedDayKernel.LaxMonoid.isCommMonObj d b S L B
    letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
    letI := hLeft
    letI := hRight
    letI := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ (n m : I) (X Y : V),
      RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
          (RightModuleFree.freeObject (⟨S⟩ : EnrichedFunctorCat V I) (Free.object n X))
          (RightModuleFree.freeObject (⟨S⟩ : EnrichedFunctorCat V I) (Free.object m Y)) ≫
        (pairFromDay d b S L B hLeft hRight n m X Y).hom.hom =
      tensorμ (Free.object n X) (⟨S⟩ : EnrichedFunctorCat V I) (Free.object m Y) ⟨S⟩ ≫
        ((Free.object n X ⊗ Free.object m Y) ◁ MonObj.mul (X := (⟨S⟩ : EnrichedFunctorCat V I))) ≫
        ((diagramPair d n m X Y).hom ▷ (⟨S⟩ : EnrichedFunctorCat V I)) := by
  let := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
  let := EnrichedDayKernel.BraidingMonoidal.symmetricCategory d b
  let := EnrichedDayKernel.LaxMonoid.monObj d S L
  let := EnrichedDayKernel.LaxMonoid.isCommMonObj d b S L B
  let : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  let := hLeft
  let := hRight
  let := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  intro n m X Y
  have hp : Primitive.OfIsoProjectionFormula (⟨S⟩ : EnrichedFunctorCat V I)
      (Free.object n X) (Free.object m Y) (Free.object (n ⊗ m) (X ⊗ Y))
      (diagramPair d n m X Y) :=
    Primitive.ofIso_projection (⟨S⟩ : EnrichedFunctorCat V I)
      (Free.object n X) (Free.object m Y) (Free.object (n ⊗ m) (X ⊗ Y))
      (diagramPair d n m X Y)
  exact hp

include b B in
/-- The complete ordinary source pair function retains the original freeObject and ofIso values. -/
def ordinaryPairFamily :
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
    letI := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ (n m : I) (X Y : V),
      Primitive.PairIsoType (⟨S⟩ : EnrichedFunctorCat V I)
        (Free.object n X) (Free.object m Y) (Free.object (n ⊗ m) (X ⊗ Y)) := by
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
  letI := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  intro n m X Y
  exact Primitive.ofIso (⟨S⟩ : EnrichedFunctorCat V I)
    (Free.object n X) (Free.object m Y) (Free.object (n ⊗ m) (X ⊗ Y))
    (diagramPair d n m X Y)

include b B in
/-- The complete evaluated source pair keeps both literal free/evaluation source objects. -/
def evaluationPairFamily :
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
    letI := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ (n m : I) (X Y : V),
      Evaluation.PairIsoType (⟨S⟩ : EnrichedFunctorCat V I) n m (n ⊗ m) X Y := by
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
  letI := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  intro n m X Y
  exact Evaluation.ofIso (⟨S⟩ : EnrichedFunctorCat V I) n m (n ⊗ m) X Y
    (diagramPair d n m X Y)

include b B in
/-- The COMPLETE original coefficient law as a statement over all original source data. -/
private def fullPairCoefficientFormula : Prop :=
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
  ∀ (n m : I) {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y'),
    Primitive.NaturalityProperty (⟨S⟩ : EnrichedFunctorCat V I)
      (Free.coefficientMap n f) (Free.coefficientMap m g)
      (Free.coefficientMap (n ⊗ m) (f ⊗ₘ g))
      (diagramPair d n m X Y) (diagramPair d n m X' Y')

include b B in
/-- Original Primitive.naturality_spec with the original complete Day coefficient compatibility. -/
private abbrev fullPairCoefficientProof : fullPairCoefficientFormula d b S L B := by
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
  change ∀ (n m : I) {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y'),
    Primitive.NaturalityProperty (⟨S⟩ : EnrichedFunctorCat V I)
      (Free.coefficientMap n f) (Free.coefficientMap m g)
      (Free.coefficientMap (n ⊗ m) (f ⊗ₘ g))
      (diagramPair d n m X Y) (diagramPair d n m X' Y')
  intro n m X X' Y Y' f g
  exact Primitive.naturality_spec (⟨S⟩ : EnrichedFunctorCat V I)
    (Free.coefficientMap n f) (Free.coefficientMap m g)
    (Free.coefficientMap (n ⊗ m) (f ⊗ₘ g))
    (diagramPair d n m X Y) (diagramPair d n m X' Y')
    (diagramPair_coefficient_spec d n m f g)

include b B in
/-- The COMPLETE original contravariant source law and its full unit-Hom tensor map. -/
private def fullPairSourceFormula : Prop :=
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
  ∀ {n n' m m' : I}
    (p : 𝟙_ V ⟶ (n ⟶[V] n')) (q : 𝟙_ V ⟶ (m ⟶[V] m')) (X Y : V),
    Primitive.NaturalityProperty (⟨S⟩ : EnrichedFunctorCat V I)
      (Free.sourceMap p X) (Free.sourceMap q Y)
      (Free.sourceMap (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ≫
        d.tensorEnrichedFunctor.map (n, m) (n', m')) (X ⊗ Y))
      (diagramPair d n' m' X Y) (diagramPair d n m X Y)

include b B in
/-- Original Primitive.naturality_spec with the entire original Day source compatibility. -/
private abbrev fullPairSourceProof : fullPairSourceFormula d b S L B := by
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
  change ∀ {n n' m m' : I}
    (p : 𝟙_ V ⟶ (n ⟶[V] n')) (q : 𝟙_ V ⟶ (m ⟶[V] m')) (X Y : V),
    Primitive.NaturalityProperty (⟨S⟩ : EnrichedFunctorCat V I)
      (Free.sourceMap p X) (Free.sourceMap q Y)
      (Free.sourceMap (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ≫
        d.tensorEnrichedFunctor.map (n, m) (n', m')) (X ⊗ Y))
      (diagramPair d n' m' X Y) (diagramPair d n m X Y)
  intro n n' m m' p q X Y
  exact Primitive.naturality_spec (⟨S⟩ : EnrichedFunctorCat V I)
    (Free.sourceMap p X) (Free.sourceMap q Y)
    (Free.sourceMap (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ≫
      d.tensorEnrichedFunctor.map (n, m) (n', m')) (X ⊗ Y))
    (diagramPair d n' m' X Y) (diagramPair d n m X Y)
    (diagramPair_source_spec d p q X Y)

include b B in
/-- Every full original two-free prequotient source retains both entire sphere multiplications. -/
theorem ordinaryPairProjectionFamily :
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
    letI := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ (n m : I) (X Y : V),
      RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
          (RightModuleFree.freeObject (⟨S⟩ : EnrichedFunctorCat V I) (Free.object n X))
          (RightModuleFree.freeObject (⟨S⟩ : EnrichedFunctorCat V I) (Free.object m Y)) ≫
        (ordinaryPairFamily d b S L B n m X Y).hom.hom =
      tensorμ (Free.object n X) (⟨S⟩ : EnrichedFunctorCat V I) (Free.object m Y) ⟨S⟩ ≫
        ((Free.object n X ⊗ Free.object m Y) ◁ MonObj.mul (X := (⟨S⟩ : EnrichedFunctorCat V I))) ≫
        ((diagramPair d n m X Y).hom ▷ (⟨S⟩ : EnrichedFunctorCat V I)) := by
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
  let := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  intro n m X Y
  exact Primitive.ofIso_projection (⟨S⟩ : EnrichedFunctorCat V I)
    (Free.object n X) (Free.object m Y) (Free.object (n ⊗ m) (X ⊗ Y))
    (diagramPair d n m X Y)

include b B in
/-- The complete original free-pair inverse retains its base inverse,
associator, unit and quotient. -/
theorem ordinaryPairInverseFamily :
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
    letI := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ (n m : I) (X Y : V),
      (ordinaryPairFamily d b S L B n m X Y).inv.hom =
        ((diagramPair d n m X Y).inv ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫
          (α_ (Free.object n X) (Free.object m Y) (⟨S⟩ : EnrichedFunctorCat V I)).hom ≫
            (RightModuleFree.freeGenerator (⟨S⟩ : EnrichedFunctorCat V I) (Free.object n X) ▷
              (Free.object m Y ⊗ (⟨S⟩ : EnrichedFunctorCat V I))) ≫
                RightModuleFree.relativeTensorπ (⟨S⟩ : EnrichedFunctorCat V I)
                  (RightModuleFree.freeObject (⟨S⟩ : EnrichedFunctorCat V I) (Free.object n X))
                  (RightModuleFree.freeObject (⟨S⟩ : EnrichedFunctorCat V I)
                    (Free.object m Y)) := by
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
  let := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  intro n m X Y
  exact Primitive.ofIso_inv (⟨S⟩ : EnrichedFunctorCat V I)
    (Free.object n X) (Free.object m Y) (Free.object (n ⊗ m) (X ⊗ Y))
    (diagramPair d n m X Y)

end PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Internal

namespace PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Selected

universe uF vF uFI vFI
open EnrichedFunctorCat
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits

variable {V : Type uF} [Category.{vF} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uFI} [Category.{vFI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uFI, uFI} V]
  [HasProducts.{uFI} V] [HasEqualizers V]
  (q : Enriched.ModuleMappingR.SelectedSource V I)

/-- The complete Day pair type at the selected enriched tensor and both coefficients. -/
def DiagramPairType :=
  letI := q.dayMonoidal
  ∀ (n m : I) (X Y : V),
    Free.object n X ⊗ Free.object m Y ≅ Free.object (n ⊗ m) (X ⊗ Y)

/-- The original complete Day pair, supplied using the named selected tensor data. -/
def diagramPair : DiagramPairType q := Internal.diagramPair q.monoidalData

/-- The whole two-free relative comparison type on the selected stock module tensor. -/
def PairIsoType :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.primitiveMonoidal
  ∀ (n m : I) (X Y : V),
    Primitive.PairIsoType q.coefficient (Free.object n X) (Free.object m Y)
      (Free.object (n ⊗ m) (X ⊗ Y))

/-- The original tensorator followed by the original full Day comparison. -/
def pair : PairIsoType q := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.primitiveMonoidal
  intro n m X Y
  exact Primitive.ofIso q.coefficient (Free.object n X) (Free.object m Y)
    (Free.object (n ⊗ m) (X ⊗ Y)) (diagramPair q n m X Y)

/-- The same whole comparison type on the actual free/evaluation source objects. -/
def EvaluationPairIsoType :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.primitiveMonoidal
  ∀ (n m : I) (X Y : V),
    Evaluation.PairIsoType q.coefficient n m (n ⊗ m) X Y

/-- The original evaluated pair supplier retains its full original source objects and maps. -/
def sourcePair : EvaluationPairIsoType q := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.primitiveMonoidal
  intro n m X Y
  exact Evaluation.ofIso q.coefficient n m (n ⊗ m) X Y (diagramPair q n m X Y)

/-- The whole coefficient equation, including all four coefficients and both morphisms. -/
def PairCoefficientFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  ∀ (n m : I) {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y'),
    Primitive.NaturalityProperty q.coefficient
      (Free.coefficientMap n f) (Free.coefficientMap m g)
      (Free.coefficientMap (n ⊗ m) (f ⊗ₘ g))
      (diagramPair q n m X Y) (diagramPair q n m X' Y')

/-- The original coefficient proof supplies the independently written whole equation. -/
abbrev pairCoefficient : PairCoefficientFormula q :=
  Internal.fullPairCoefficientProof q.monoidalData q.braidedData q.coefficientFunctor
    q.coefficientMonoidal q.coefficientBraided

/-- Both original contravariant source points and their full unit-Hom tensor equation. -/
def PairSourceFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  ∀ {n n' m m' : I}
    (p : 𝟙_ V ⟶ (n ⟶[V] n')) (r : 𝟙_ V ⟶ (m ⟶[V] m')) (X Y : V),
    Primitive.NaturalityProperty q.coefficient
      (Free.sourceMap p X) (Free.sourceMap r Y)
      (Free.sourceMap (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ r)) ≫
        q.monoidalData.tensorEnrichedFunctor.map (n, m) (n', m')) (X ⊗ Y))
      (diagramPair q n' m' X Y) (diagramPair q n m X Y)

/-- The original source-index proof supplies the whole selected source equation. -/
abbrev pairSource : PairSourceFormula q :=
  Internal.fullPairSourceProof q.monoidalData q.braidedData q.coefficientFunctor
    q.coefficientMonoidal q.coefficientBraided

/-- The complete prequotient equation contains both sphere factors and their multiplication. -/
def PairProjectionFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.primitiveMonoidal
  ∀ (n m : I) (X Y : V),
    Primitive.OfIsoProjectionFormula q.coefficient
      (Free.object n X) (Free.object m Y) (Free.object (n ⊗ m) (X ⊗ Y))
      (diagramPair q n m X Y)

/-- The original quotient theorem supplies the independently written full projection equation. -/
theorem pairProjection : PairProjectionFormula q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.primitiveMonoidal
  intro n m X Y
  exact Primitive.ofIso_projection q.coefficient (Free.object n X) (Free.object m Y)
    (Free.object (n ⊗ m) (X ⊗ Y)) (diagramPair q n m X Y)

/-- The complete inverse contains the original Day inverse, associator, unit and quotient. -/
def PairInverseFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.primitiveMonoidal
  ∀ (n m : I) (X Y : V),
    Primitive.OfIsoInverseFormula q.coefficient
      (Free.object n X) (Free.object m Y) (Free.object (n ⊗ m) (X ⊗ Y))
      (diagramPair q n m X Y)

/-- The actual original inverse theorem supplies the complete selected inverse formula. -/
theorem pairInverse : PairInverseFormula q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.primitiveMonoidal
  intro n m X Y
  exact Primitive.ofIso_inv q.coefficient (Free.object n X) (Free.object m Y)
    (Free.object (n ⊗ m) (X ⊗ Y)) (diagramPair q n m X Y)

end PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Selected


namespace PointedCGWH.Spectra.Orthogonal.SphereSmashFree

/-- The continuous isometry category used by the original orthogonal source. -/
local instance : Category.{v} OrthogonalIndex := SphereSmashStructure.indexCategory.{u, v}
/-- The original direct sum tensor on the continuous orthogonal index. -/
local instance : MonoidalCategory OrthogonalIndex :=
  SphereSmashStructure.indexMonoidalCategory.{u, v}
/-- The pointed continuous enrichment of the original orthogonal index. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  SphereSmashStructure.indexEnrichedOrdinaryCategory.{u, v}
/-- The original block symmetry of the continuous orthogonal index. -/
local instance : SymmetricCategory OrthogonalIndex :=
  SphereSmashStructure.indexSymmetricCategory.{u, v}
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits

private abbrev V := PointedCGWH.{u, v}
/-- Continuous orthogonal spaces with their original enriched Hom actions. -/
abbrev ISpace := EnrichedFunctorCat V.{u, v} OrthogonalIndex

/-- The continuous Day tensor on the original orthogonal spaces. -/
local instance : MonoidalCategory ISpace.{u, v} := SphereSmashStructure.dayMonoidalCategory.{u, v}
/-- The original continuous Day symmetry on orthogonal spaces. -/
local instance : SymmetricCategory ISpace.{u, v} := SphereSmashStructure.daySymmetricCategory.{u, v}
/-- The original representation sphere monoid for the continuous Day tensor. -/
local instance : MonObj sphereISpace.{u, v} := SphereSmashStructure.sphereMonoid.{u, v}
local instance : IsCommMonObj sphereISpace.{u, v} :=
  SphereSmashStructure.sphereCommutativeMonoid.{u, v}
local instance : HasCoequalizers ISpace.{u, v} := SphereSmashStructure.spaceCoequalizers.{u, v}
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}
/-- The relative sphere tensor selected by the complete native factory. -/
local instance : MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmashStructure.monoidalCategory.{u, v}

/-- The actual full Day pair on the original continuous free orthogonal I-spaces. -/
abbrev diagramPair : Selected.DiagramPairType SphereSmash.sourceData.{u, v} :=
  Selected.diagramPair SphereSmash.sourceData.{u, v}

/-- The stock free right sphere module, with its original free/evaluation adjunction. -/
abbrev freeObject := CanonicalSourceRightModuleFreeEvaluation.freeObject.{u, v}

/-- The original index tensor object with both native universe suppliers fixed explicitly. -/
def tensorIndex (n m : OrthogonalIndex) : OrthogonalIndex :=
  @MonoidalCategoryStruct.tensorObj OrthogonalIndex (SphereSmash.sourceData.{u, v}).indexCategory
    (SphereSmash.sourceData.{u, v}).indexMonoidal.toMonoidalCategoryStruct n m

/-- The native tensor index is the original sum of representation dimensions. -/
theorem tensorIndex_eq_add (n m : OrthogonalIndex) : tensorIndex.{u, v} n m = n + m := rfl

/-- The actual free sphere-smash comparison retains all original objects and maps. -/
def pairIso : Selected.PairIsoType SphereSmash.sourceData.{u, v} :=
  Selected.pair SphereSmash.sourceData.{u, v}

/-- The same original comparison retains the actual free/evaluation source objects. -/
def sourcePairIso : Selected.EvaluationPairIsoType SphereSmash.sourceData.{u, v} :=
  Selected.sourcePair SphereSmash.sourceData.{u, v}

/-- Both whole original coefficient maps are retained by the native free sphere smash. -/
abbrev pairIsoCoefficient : Selected.PairCoefficientFormula SphereSmash.sourceData.{u, v} :=
  Selected.pairCoefficient SphereSmash.sourceData.{u, v}

/-- Both entire source-index maps retain their original continuous Hom and tensor coefficients. -/
abbrev pairIsoSource : Selected.PairSourceFormula SphereSmash.sourceData.{u, v} :=
  Selected.pairSource SphereSmash.sourceData.{u, v}

/-- The complete original prequotient free-smash projection formula. -/
abbrev pairIsoProjection : Selected.PairProjectionFormula SphereSmash.sourceData.{u, v} :=
  Selected.pairProjection SphereSmash.sourceData.{u, v}

/-- The complete native inverse retains the actual source unit insertion and quotient maps. -/
abbrev pairIsoInv : Selected.PairInverseFormula SphereSmash.sourceData.{u, v} :=
  Selected.pairInverse SphereSmash.sourceData.{u, v}

end PointedCGWH.Spectra.Orthogonal.SphereSmashFree
