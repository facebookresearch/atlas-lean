/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceFreeSmash

/-!
# The full original orthogonal free-pair bifunctor

The complete source Day pair, original free/evaluation comparisons and both
equivalence units assemble the actual native pair as a natural isomorphism.
The construction is first checked on the original module boundary, where the
given original coefficient equations have their full abstract types.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.ModuleStage

universe uV vV uI uJ

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)]
  [SymmetricCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {J : Type uJ} [EnrichedCategory V J]
  (E : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
  (a : I → J)
  (h : ∀ n, E.functor ⋙ evaluation (a n) ≅
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)

/-- The original source pair and all of its coefficient squares give the entire
native bifunctor comparison through the actual original module equivalence. -/
def functorIso (n m r : I)
    (e : ∀ X Y : V, Free.object n X ⊗ Free.object m Y ≅ Free.object r (X ⊗ Y))
    (he : ∀ ⦃X X' Y Y' : V⦄ (f : X ⟶ X') (g : Y ⟶ Y'),
      Orthogonal.SphereSmashFree.Primitive.Compatible
        (Free.coefficientMap n f) (Free.coefficientMap m g)
        (Free.coefficientMap r (f ⊗ₘ g)) (e X Y) (e X' Y')) :
    letI := RightModuleFree.tensorMonoidal S
    letI := Monoidal.transport E
    (Free.functor (a n)).prod (Free.functor (a m)) ⋙ tensor (EnrichedFunctorCat V J) ≅
      tensor V ⋙ Free.functor (a r) := by
  letI := RightModuleFree.tensorMonoidal S
  letI := Monoidal.transport E
  refine NatIso.ofComponents (fun p =>
    Orthogonal.CanonicalSourceFreeSmash.ModuleStage.ofIso S E a h
      n m r p.1 p.2 (e p.1 p.2)) ?_
  intro p q f
  exact Orthogonal.CanonicalSourceFreeSmash.ModuleStage.coefficient_spec S E a h
    n m r f.1 f.2 (e p.1 p.2) (e q.1 q.2) (he f.1 f.2)

/-- The whole forward component is the given original reconstruction. -/
theorem functorIso_hom_app (n m r : I)
    (e : ∀ X Y : V, Free.object n X ⊗ Free.object m Y ≅ Free.object r (X ⊗ Y))
    (he : ∀ ⦃X X' Y Y' : V⦄ (f : X ⟶ X') (g : Y ⟶ Y'),
      Orthogonal.SphereSmashFree.Primitive.Compatible
        (Free.coefficientMap n f) (Free.coefficientMap m g)
        (Free.coefficientMap r (f ⊗ₘ g)) (e X Y) (e X' Y')) (X Y : V) :
    letI := RightModuleFree.tensorMonoidal S
    letI := Monoidal.transport E
    (functorIso S E a h n m r e he).hom.app (X, Y) =
      (Orthogonal.CanonicalSourceFreeSmash.ModuleStage.ofIso S E a h
        n m r X Y (e X Y)).hom := rfl

/-- The whole inverse component is the same original inverse reconstruction. -/
theorem functorIso_inv_app (n m r : I)
    (e : ∀ X Y : V, Free.object n X ⊗ Free.object m Y ≅ Free.object r (X ⊗ Y))
    (he : ∀ ⦃X X' Y Y' : V⦄ (f : X ⟶ X') (g : Y ⟶ Y'),
      Orthogonal.SphereSmashFree.Primitive.Compatible
        (Free.coefficientMap n f) (Free.coefficientMap m g)
        (Free.coefficientMap r (f ⊗ₘ g)) (e X Y) (e X' Y')) (X Y : V) :
    letI := RightModuleFree.tensorMonoidal S
    letI := Monoidal.transport E
    (functorIso S E a h n m r e he).inv.app (X, Y) =
      (Orthogonal.CanonicalSourceFreeSmash.ModuleStage.ofIso S E a h
        n m r X Y (e X Y)).inv := rfl

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.ModuleStage

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.ModuleStage.FullFunctorFamily

universe uV vV uI uJ

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)]
  [SymmetricCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {J : Type uJ} [EnrichedCategory V J]
  (E : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
  (a : I → J)
  (h : ∀ n, E.functor ⋙ evaluation (a n) ≅
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)

/-- The entire original comparison between both coefficient functors and the target coefficient tensor. -/
def FamilyType (t : I → I → I) : Type _ :=
  letI := RightModuleFree.tensorMonoidal S
  letI := Monoidal.transport E
  ∀ (r s : I),
    (Free.functor (a r)).prod (Free.functor (a s)) ⋙ tensor (EnrichedFunctorCat V J) ≅
      tensor V ⋙ Free.functor (a (t r s))

/-- The complete original source construction, with every comparison and coefficient square. -/
def originalFamily (t : I → I → I)
    (comparison : ∀ (r s : I) (X Y : V),
      Free.object r X ⊗ Free.object s Y ≅ Free.object (t r s) (X ⊗ Y))
    (naturality : ∀ (r s : I) ⦃X X' Y Y' : V⦄ (f : X ⟶ X') (g : Y ⟶ Y'),
      Orthogonal.SphereSmashFree.Primitive.Compatible
        (Free.coefficientMap r f) (Free.coefficientMap s g)
        (Free.coefficientMap (t r s) (f ⊗ₘ g))
        (comparison r s X Y) (comparison r s X' Y')) :
    FamilyType S E a t :=
  fun r s => PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.ModuleStage.functorIso
    S E a h r s (t r s) (comparison r s) (naturality r s)


/-- The entire original hom component equation, for every complete symbolic source pair. -/
def homFamilyType (t : I → I → I)
    (comparison : ∀ (r s : I) (X Y : V),
      Free.object r X ⊗ Free.object s Y ≅ Free.object (t r s) (X ⊗ Y))
    (naturality : ∀ (r s : I) ⦃X X' Y Y' : V⦄ (f : X ⟶ X') (g : Y ⟶ Y'),
      Orthogonal.SphereSmashFree.Primitive.Compatible
        (Free.coefficientMap r f) (Free.coefficientMap s g)
        (Free.coefficientMap (t r s) (f ⊗ₘ g))
        (comparison r s X Y) (comparison r s X' Y')) :
    Prop :=
  letI := RightModuleFree.tensorMonoidal S
  letI := Monoidal.transport E
  ∀ (r s : I) (X Y : V),
    (originalFamily S E a h t comparison naturality r s).hom.app (X, Y) =
      (Orthogonal.CanonicalSourceFreeSmash.ModuleStage.ofIso S E a h
        r s (t r s) X Y (comparison r s X Y)).hom

/-- The original complete component theorem supplies all source components. -/
theorem homFamily (t : I → I → I)
    (comparison : ∀ (r s : I) (X Y : V),
      Free.object r X ⊗ Free.object s Y ≅ Free.object (t r s) (X ⊗ Y))
    (naturality : ∀ (r s : I) ⦃X X' Y Y' : V⦄ (f : X ⟶ X') (g : Y ⟶ Y'),
      Orthogonal.SphereSmashFree.Primitive.Compatible
        (Free.coefficientMap r f) (Free.coefficientMap s g)
        (Free.coefficientMap (t r s) (f ⊗ₘ g))
        (comparison r s X Y) (comparison r s X' Y')) :
    homFamilyType S E a h t comparison naturality :=
  fun r s X Y => PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.ModuleStage.functorIso_hom_app
    S E a h r s (t r s) (comparison r s) (naturality r s) X Y


/-- The entire original inv component equation, for every complete symbolic source pair. -/
def invFamilyType (t : I → I → I)
    (comparison : ∀ (r s : I) (X Y : V),
      Free.object r X ⊗ Free.object s Y ≅ Free.object (t r s) (X ⊗ Y))
    (naturality : ∀ (r s : I) ⦃X X' Y Y' : V⦄ (f : X ⟶ X') (g : Y ⟶ Y'),
      Orthogonal.SphereSmashFree.Primitive.Compatible
        (Free.coefficientMap r f) (Free.coefficientMap s g)
        (Free.coefficientMap (t r s) (f ⊗ₘ g))
        (comparison r s X Y) (comparison r s X' Y')) :
    Prop :=
  letI := RightModuleFree.tensorMonoidal S
  letI := Monoidal.transport E
  ∀ (r s : I) (X Y : V),
    (originalFamily S E a h t comparison naturality r s).inv.app (X, Y) =
      (Orthogonal.CanonicalSourceFreeSmash.ModuleStage.ofIso S E a h
        r s (t r s) X Y (comparison r s X Y)).inv

/-- The original complete component theorem supplies all source components. -/
theorem invFamily (t : I → I → I)
    (comparison : ∀ (r s : I) (X Y : V),
      Free.object r X ⊗ Free.object s Y ≅ Free.object (t r s) (X ⊗ Y))
    (naturality : ∀ (r s : I) ⦃X X' Y Y' : V⦄ (f : X ⟶ X') (g : Y ⟶ Y'),
      Orthogonal.SphereSmashFree.Primitive.Compatible
        (Free.coefficientMap r f) (Free.coefficientMap s g)
        (Free.coefficientMap (t r s) (f ⊗ₘ g))
        (comparison r s X Y) (comparison r s X' Y')) :
    invFamilyType S E a h t comparison naturality :=
  fun r s X Y => PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.ModuleStage.functorIso_inv_app
    S E a h r s (t r s) (comparison r s) (naturality r s) X Y

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.ModuleStage.FullFunctorFamily

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.SelectedBifunctor

universe uV vV uI vI uJ
open EnrichedFunctorCat
open PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]
  {q : Enriched.ModuleMappingR.SelectedSource V I}
  {J : Type uJ} [EnrichedCategory V J] (c : SelectedPair.Context q J)

/-- The entire original pair comparison between both complete coefficient functors. -/
def FamilyType : Type _ :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  letI := q.primitiveMonoidal
  letI := Monoidal.transport c.sourceEquivalence
  ∀ (r s : I),
    (Free.functor (c.indexMap r)).prod (Free.functor (c.indexMap s)) ⋙
        tensor (EnrichedFunctorCat V J) ≅
      tensor V ⋙ Free.functor (c.indexMap (c.tensorIndex r s))

/-- The whole original natural isomorphism at the separately stated typed context. -/
def functorIso : FamilyType c := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  exact ModuleStage.FullFunctorFamily.originalFamily q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison c.tensorIndex c.diagramPair c.diagramPairCoefficient

/-- The complete original hom component equation for the entire coefficient bifunctor. -/
def HomFormulaType : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  ModuleStage.FullFunctorFamily.homFamilyType q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison c.tensorIndex c.diagramPair c.diagramPairCoefficient

/-- The full original hom component theorem, supplied at its independent typed formula. -/
theorem hom : HomFormulaType c := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  exact ModuleStage.FullFunctorFamily.homFamily q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison c.tensorIndex c.diagramPair c.diagramPairCoefficient

/-- The complete original inv component equation for the entire coefficient bifunctor. -/
def InvFormulaType : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  ModuleStage.FullFunctorFamily.invFamilyType q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison c.tensorIndex c.diagramPair c.diagramPairCoefficient

/-- The full original inv component theorem, supplied at its independent typed formula. -/
theorem inv : InvFormulaType c := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  exact ModuleStage.FullFunctorFamily.invFamily q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison c.tensorIndex c.diagramPair c.diagramPairCoefficient

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.SelectedBifunctor

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair

universe u v

open PointedCGWH.Spectra.Orthogonal
open CategoryTheory.Spectra.OrthogonalSourceRightModule

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

private abbrev ISpace := EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex
/-- The continuous Day tensor on the original orthogonal spaces. -/
local instance : MonoidalCategory ISpace.{u, v} := SphereSmashStructure.dayMonoidalCategory.{u, v}
/-- The original continuous Day symmetry on orthogonal spaces. -/
local instance : SymmetricCategory ISpace.{u, v} := SphereSmashStructure.daySymmetricCategory.{u, v}
/-- The original representation sphere monoid for the continuous Day tensor. -/
local instance : MonObj sphereISpace.{u, v} := SphereSmashStructure.sphereMonoid.{u, v}
local instance : IsCommMonObj sphereISpace.{u, v} :=
  SphereSmashStructure.sphereCommutativeMonoid.{u, v}
local instance : HasCoequalizers ISpace.{u, v} := SphereSmashStructure.hasCoequalizers.{u, v}

local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}

/-- The genuine Day adjunction supplies preservation in the first coefficient. -/
theorem nativeTensorLeftPreserves :
    (SphereSmash.sourceData.{u, v}).DayTensorLeftPreservationType :=
  (SphereSmash.sourceData.{u, v}).dayTensorLeftPreserves
attribute [local instance] nativeTensorLeftPreserves

/-- The same genuine Day adjunction supplies preservation in the second coefficient. -/
theorem nativeTensorRightPreserves :
    (SphereSmash.sourceData.{u, v}).DayTensorRightPreservationType :=
  (SphereSmash.sourceData.{u, v}).dayTensorRightPreserves
attribute [local instance] nativeTensorRightPreserves

/-- The relative sphere tensor selected by the complete native factory. -/
local instance : MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmashStructure.monoidalCategory.{u, v}
/-- The native sphere tensor transported through the original source equivalence. -/
local instance : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The complete original ordinary type of the actual coefficient bifunctor comparison. -/
def FunctorIsoFormulaType : Type _ := SelectedBifunctor.FamilyType CanonicalSourceFreeSmash.pairData.{u, v}

/-- The whole genuine native pair family is natural in both original coefficients. -/
def functorIso : FunctorIsoFormulaType.{u, v} :=
  SelectedBifunctor.functorIso CanonicalSourceFreeSmash.pairData.{u, v}

/-- The entire forward component equality for the actual original bifunctor. -/
def FunctorIsoHomFormulaType : Prop := SelectedBifunctor.HomFormulaType CanonicalSourceFreeSmash.pairData.{u, v}

/-- Every forward component is the same entire original native free-pair map. -/
theorem functorIso_hom_app : FunctorIsoHomFormulaType.{u, v} :=
  SelectedBifunctor.hom CanonicalSourceFreeSmash.pairData.{u, v}

/-- The entire inverse component equality for the actual original bifunctor. -/
def FunctorIsoInvFormulaType : Prop := SelectedBifunctor.InvFormulaType CanonicalSourceFreeSmash.pairData.{u, v}

/-- Every inverse component is the same entire original inverse native free-pair map. -/
theorem functorIso_inv_app : FunctorIsoInvFormulaType.{u, v} :=
  SelectedBifunctor.inv CanonicalSourceFreeSmash.pairData.{u, v}

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair
