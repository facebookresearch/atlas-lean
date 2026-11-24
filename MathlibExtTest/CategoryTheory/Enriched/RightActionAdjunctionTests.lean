/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.CategoryTheory.Enriched.ProductRelationMapping
import MathlibExt.CategoryTheory.Enriched.EnrichedHomTransport
import MathlibExt.CategoryTheory.Enriched.EnrichedAdjunctionValue
import MathlibExt.CategoryTheory.Enriched.RightActionMappingCategory
import MathlibExt.CategoryTheory.Enriched.EnrichedRightMappingCategory
import MathlibExt.CategoryTheory.Monoidal.CommutativeModuleConversion
import MathlibExt.CategoryTheory.Monoidal.RightModuleFree
import MathlibExt.CategoryTheory.Enriched.FreeEvaluation

set_option autoImplicit false
noncomputable section
universe uV vV uC uI uR
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.RightActionAdjunctionOwner

section ProductRelations
variable {V : Type uV} [Category.{vV} V] {I : Type uI} {R : Type uR}
  (d : Enriched.ProductRelationMapping.Data (V := V) (I := I) (R := R))
  [HasProduct d.objects] [HasProduct d.relations]
  [HasEqualizer (Enriched.ProductRelationMapping.leftMap d)
    (Enriched.ProductRelationMapping.rightMap d)]

example (P : V) (q : Enriched.ProductRelationMapping.Family d P) (i : I) :
    Enriched.ProductRelationMapping.lift d q ≫ Enriched.ProductRelationMapping.π d i = q.app i :=
  Enriched.ProductRelationMapping.lift_π d q i

example (P : V) (q : Enriched.ProductRelationMapping.Family d P) :
    Enriched.ProductRelationMapping.toFamily d (Enriched.ProductRelationMapping.lift d q) = q :=
  Enriched.ProductRelationMapping.toFamily_lift d q

example (P : V) (f : P ⟶ Enriched.ProductRelationMapping.Hom d) :
    Enriched.ProductRelationMapping.lift d (Enriched.ProductRelationMapping.toFamily d f) = f :=
  Enriched.ProductRelationMapping.lift_toFamily d f
end ProductRelations

section EnrichedAdjunction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {C : Type uC} [Category C] [EnrichedOrdinaryCategory V C]
  {L : V ⥤ C} {R : C ⥤ V} (d : EnrichedAdjunctionHom.Data L R)
  (adj : L ⊣ R) (sep : IsSeparator (𝟙_ V))

example (X : V) (M : C) :
    (EnrichedAdjunctionHom.Full.homIso d adj sep X M).hom ≫
      (EnrichedAdjunctionHom.Full.homIso d adj sep X M).inv = 𝟙 _ :=
  EnrichedAdjunctionHom.Full.forward_inverse d adj sep X M

example (X : V) (M : C) :
    (EnrichedAdjunctionHom.Full.homIso d adj sep X M).inv ≫
      (EnrichedAdjunctionHom.Full.homIso d adj sep X M).hom = 𝟙 _ :=
  EnrichedAdjunctionHom.Full.inverse_forward d adj sep X M

example (X : V) (M : C) (f : L.obj X ⟶ M) :
    eHomEquiv V f ≫ EnrichedAdjunctionHom.Full.forward d adj X M =
      eHomEquiv V (adj.homEquiv X M f) :=
  EnrichedAdjunctionHom.Full.forward_point d adj X M f

example (X : V) (M : C) (f : X ⟶ R.obj M) :
    eHomEquiv V f ≫ EnrichedAdjunctionHom.Full.inverse d adj X M =
      eHomEquiv V ((adj.homEquiv X M).symm f) :=
  EnrichedAdjunctionHom.Full.inverse_point d adj X M f

example (M : C) (f : L.obj (𝟙_ V) ⟶ M) :
    eHomEquiv V f ≫ (EnrichedAdjunctionHom.Full.valueIso d adj sep M).hom =
      adj.homEquiv (𝟙_ V) M f :=
  EnrichedAdjunctionHom.UnitValue.valueIso_point d adj sep M f

example (X : V) : eCoyoneda V (L.obj X) ≅ R ⋙ ihom X :=
  EnrichedAdjunctionHom.UnitValue.homNatIso d adj sep X

example : eCoyoneda V (L.obj (𝟙_ V)) ≅ R :=
  EnrichedAdjunctionHom.UnitValue.valueNatIso d adj sep

example (X : V) (M N : C) :
    eComp V (L.obj X) M N ≫ EnrichedAdjunctionHom.Full.forward d adj X N =
      (EnrichedAdjunctionHom.Full.forward d adj X M ⊗ₘ d.rightMap M N) ≫
        eComp V X (R.obj M) (R.obj N) :=
  EnrichedAdjunctionHom.Full.forward_target d adj sep X M N
end EnrichedAdjunction

section OriginalHomTransport
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [EnrichedCategory V C] (Q : C → C → V)
  (e : ∀ X Y : C, (X ⟶[V] Y) ≅ Q X Y)

example : EnrichedCategory V (EnrichedHomTransport.Objects Q e) :=
  EnrichedHomTransport.enrichedCategory Q e
end OriginalHomTransport

section OrdinaryRightMappings
open Enriched.RightActionMappingCategory
universe vI
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] {C : Type uC}
  (d : Enriched.RightActionMappingCategory.Data (V := V) (I := I) C)
  [∀ M N, HasProduct (Enriched.RightActionMapping.objects (mappingData d M N))]
  [∀ M N, HasProduct (Enriched.RightActionMapping.relations (mappingData d M N))]
  [∀ M N, HasEqualizer (Enriched.RightActionMapping.leftMap (mappingData d M N))
    (Enriched.RightActionMapping.rightMap (mappingData d M N))]

example (M : C) (n : I) : identity d M ≫ π d M M n = eId V ((d.diagram M).obj n) :=
  identity_π d M n

example (M N P : C) (n : I) : composition d M N P ≫ π d M P n =
    (π d M N n ⊗ₘ π d N P n) ≫
      eComp V ((d.diagram M).obj n) ((d.diagram N).obj n) ((d.diagram P).obj n) :=
  composition_π d M N P n

example (M N : C) :
    (λ_ (Hom d M N)).inv ≫ identity d M ▷ Hom d M N ≫ composition d M M N = 𝟙 _ :=
  identity_composition d M N

example (M N : C) :
    (ρ_ (Hom d M N)).inv ≫ Hom d M N ◁ identity d N ≫ composition d M N N = 𝟙 _ :=
  composition_identity d M N

example (W M N P : C) :
    (α_ (Hom d W M) (Hom d M N) (Hom d N P)).inv ≫
      composition d W M N ▷ Hom d N P ≫ composition d W N P =
        Hom d W M ◁ composition d M N P ≫ composition d W M P :=
  composition_associativity d W M N P

example : EnrichedCategory V C := Enriched.RightActionMappingCategory.enrichedCategory d
end OrdinaryRightMappings

section EnrichedRightMappings
open Enriched.EnrichedRightMappingCategory
universe uA
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I] {A : Type uA} {C : Type uC}
  (d : Enriched.EnrichedRightMappingCategory.Data (V := V) (I := I) (A := A) C)
  [∀ M N, HasProduct (system d M N).objects]
  [∀ M N, HasProduct (system d M N).relations]
  [∀ M N, HasEqualizer (Enriched.ProductRelationMapping.leftMap (system d M N))
    (Enriched.ProductRelationMapping.rightMap (system d M N))]

example (M : C) (n : I) : identity d M ≫ π d M M n = eId V ((d.diagram M).obj n) :=
  identity_π d M n

example (M N P : C) (n : I) : composition d M N P ≫ π d M P n =
    (π d M N n ⊗ₘ π d N P n) ≫
      eComp V ((d.diagram M).obj n) ((d.diagram N).obj n) ((d.diagram P).obj n) :=
  composition_π d M N P n

example (M N : C) :
    (λ_ (Hom d M N)).inv ≫ identity d M ▷ Hom d M N ≫ composition d M M N = 𝟙 _ :=
  identity_composition d M N

example (M N : C) :
    (ρ_ (Hom d M N)).inv ≫ Hom d M N ◁ identity d N ≫ composition d M N N = 𝟙 _ :=
  composition_identity d M N

example (M N : C) (P : V) (f : P ⟶ Hom d M N) (n : I) :
    (parameterEquiv d M N P f).app n = f ≫ π d M N n :=
  parameterEquiv_app d M N P f n

example (M N : C) (P : V)
    (q : Enriched.EnrichedRightActionMapping.Family (mappingData d M N) P) (n : I) :
    (parameterEquiv d M N P).symm q ≫ π d M N n = q.app n :=
  parameterEquiv_symm_π d M N P q n

example (M : C) :
    compatibleHomEquiv d M M (identityCompatible d M) = identity d M :=
  compatibleHomEquiv_identity d M

example {M N P : C}
    (f : Enriched.EnrichedRightActionMapping.CompatibleHom (mappingData d M N))
    (g : Enriched.EnrichedRightActionMapping.CompatibleHom (mappingData d N P)) :
    compatibleHomEquiv d M P (compositionCompatible d f g) = (λ_ (𝟙_ V)).inv ≫
      (compatibleHomEquiv d M N f ⊗ₘ compatibleHomEquiv d N P g) ≫ composition d M N P :=
  compatibleHomEquiv_composition d f g

example : EnrichedCategory V C := Enriched.EnrichedRightMappingCategory.enrichedCategory d
end EnrichedRightMappings

section BraidedConversion
open CommutativeModuleConversion
open scoped _root_.CategoryTheory.MonObj
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category C] [MonoidalCategory C] [BraidedCategory C]
  (S : C) [MonObj S]

example (M : Mod C S) :
    (M.X ◁ (η : (𝟙_ C) ⟶ S)) ≫ rightAction S M = (ρ_ M.X).hom :=
  rightAction_one S M

variable [IsCommMonObj S]

example (M : Mod C S) :
    (M.X ◁ (μ : S ⊗ S ⟶ S)) ≫ rightAction S M =
      (α_ M.X S S).inv ≫ (rightAction S M ▷ S) ≫ rightAction S M :=
  rightAction_mul S M

example {M N : Mod C S} (f : M ⟶ N) : (toRightMap S f).hom = f.hom :=
  toRightMap_hom S f

example {M N : RightModule S} (f : M ⟶ N) : (toLeftMap S f).hom = f.hom :=
  toLeftMap_hom S f

example (M : Mod C S) : (leftToRight S).map (𝟙 M) = 𝟙 ((leftToRight S).obj M) :=
  (leftToRight S).map_id M

example {M N P : Mod C S} (f : M ⟶ N) (g : N ⟶ P) :
    (leftToRight S).map (f ≫ g) = (leftToRight S).map f ≫ (leftToRight S).map g :=
  (leftToRight S).map_comp f g

example {M N P : RightModule S} (f : M ⟶ N) (g : N ⟶ P) :
    (rightToLeft S).map (f ≫ g) = (rightToLeft S).map f ≫ (rightToLeft S).map g :=
  (rightToLeft S).map_comp f g
end BraidedConversion

section SymmetricRecovery
open CommutativeModuleConversion
open scoped _root_.CategoryTheory.MonObj
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category C] [MonoidalCategory C] [SymmetricCategory C]
  (S : C) [MonObj S] [IsCommMonObj S]

example (M : Mod C S) : (leftRecoveryIso S M).hom.hom = 𝟙 M.X :=
  leftRecoveryIso_hom S M

example (M : RightModule S) : (rightRecoveryIso S M).inv.hom = 𝟙 M.X :=
  rightRecoveryIso_inv S M

example {M N : Mod C S} (f : M ⟶ N) :
    (rightToLeft S).map ((leftToRight S).map f) =
      (leftRecoveryIso S M).hom ≫ f ≫ (leftRecoveryIso S N).inv :=
  moduleEquivalence_left_map_inverse S f

example {M N : RightModule S} (f : M ⟶ N) :
    (leftToRight S).map ((rightToLeft S).map f) =
      (rightRecoveryIso S M).hom ≫ f ≫ (rightRecoveryIso S N).inv :=
  moduleEquivalence_right_map_inverse S f

example (M : Mod C S) :
    (leftToRight S).map ((moduleEquivalence S).unitIso.hom.app M) ≫
      (moduleEquivalence S).counitIso.hom.app ((leftToRight S).obj M) =
        𝟙 ((leftToRight S).obj M) :=
  moduleEquivalence_right_triangle S M

example (M : RightModule S) :
    (moduleEquivalence S).unitIso.hom.app ((rightToLeft S).obj M) ≫
      (rightToLeft S).map ((moduleEquivalence S).counitIso.hom.app M) =
        𝟙 ((rightToLeft S).obj M) :=
  moduleEquivalence_left_triangle S M

example (X : C) :
    (RightModuleFree.convertedLeftAdjunction S).unit.app X ≫
      (Mod.forget (D := C) (MonoidalOpposite.mop S)).map
        ((RightModuleFree.freeComparison S).hom.app X) =
          (RightModuleFree.adjunction S).unit.app X :=
  RightModuleFree.freeComparison_unit S X

example (M : RightModuleFree.Carrier S) :
    (RightModuleFree.freeComparison S).hom.app
        ((Mod.forget (D := C) (MonoidalOpposite.mop S)).obj M) ≫
      (RightModuleFree.adjunction S).counit.app M =
        (RightModuleFree.convertedLeftAdjunction S).counit.app M :=
  RightModuleFree.freeComparison_counit S M
end SymmetricRecovery

section StandardRightFree
open scoped _root_.CategoryTheory.MonObj
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category C] [MonoidalCategory C] (S : C) [MonObj S]

example (X : C) : ((RightModuleFree.functor S).obj X).X = X ⊗ S :=
  RightModuleFree.functor_obj S X

example {X Y : C} (f : X ⟶ Y) :
    eqToHom (RightModuleFree.functor_obj S X).symm ≫ ((RightModuleFree.functor S).map f).hom ≫
      eqToHom (RightModuleFree.functor_obj S Y) = f ▷ S :=
  RightModuleFree.functor_map S f

example (X : C) :
    (eqToHom (RightModuleFree.functor_obj S X).symm ▷ S) ≫
      ModObj.smul (M := MonoidalOpposite.mop S) (X := ((RightModuleFree.functor S).obj X).X) ≫
        eqToHom (RightModuleFree.functor_obj S X) =
          (α_ X S S).hom ≫ (X ◁ (μ : S ⊗ S ⟶ S)) :=
  RightModuleFree.functor_smul S X

example (X : C) :
    (RightModuleFree.functor S).map ((RightModuleFree.adjunction S).unit.app X) ≫
      (RightModuleFree.adjunction S).counit.app ((RightModuleFree.functor S).obj X) = 𝟙 _ :=
  RightModuleFree.adjunction_functor_triangle S X

example (M : RightModuleFree.Carrier S) :
    (RightModuleFree.adjunction S).unit.app
        ((Mod.forget (D := C) (MonoidalOpposite.mop S)).obj M) ≫
      (Mod.forget (D := C) (MonoidalOpposite.mop S)).map
        ((RightModuleFree.adjunction S).counit.app M) = 𝟙 _ :=
  RightModuleFree.adjunction_forget_triangle S M
end StandardRightFree

section EnrichedFreeValues
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {I : Type uI} [EnrichedCategory V I]

example (a b : I) :
    EnrichedFunctorCat.Free.functor (V := V) a ⋙ EnrichedFunctorCat.evaluation b ≅
      tensorRight (a ⟶[V] b) :=
  EnrichedFunctorCat.Free.ValueFunctor.freeValueIso a b

example (a b : I) (X : V) :
    (EnrichedFunctorCat.Free.ValueFunctor.freeValueIso a b).hom.app X =
      eqToHom (EnrichedFunctorCat.Free.object_obj a b X) := by rfl

example (a b : I) {X Y : V} (f : X ⟶ Y) :
    (EnrichedFunctorCat.Free.functor (V := V) a ⋙ EnrichedFunctorCat.evaluation b).map f ≫
        (EnrichedFunctorCat.Free.ValueFunctor.freeValueIso a b).hom.app Y =
      (EnrichedFunctorCat.Free.ValueFunctor.freeValueIso a b).hom.app X ≫
        (tensorRight (a ⟶[V] b)).map f :=
  (EnrichedFunctorCat.Free.ValueFunctor.freeValueIso a b).hom.naturality f
end EnrichedFreeValues

section OrdinaryLeftRelations
universe vI
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  (d : Enriched.RightActionMapping.Data (V := V) (I := I))
  [HasProduct (Enriched.RightActionMapping.objects d)]
  [HasProduct (Enriched.RightActionMapping.relations d)]

example (r : Enriched.RightActionMapping.Relation (I := I)) :
    Enriched.RightActionMapping.leftMap d ≫
        Pi.π (Enriched.RightActionMapping.relations d) r =
      Enriched.RightActionMapping.familyLeft d
        (Pi.π (Enriched.RightActionMapping.objects d)) r :=
  Enriched.RightActionMapping.leftMap_π d r

example {P Q : V} (f : P ⟶ Q)
    (q : ∀ n, Q ⟶ Enriched.RightActionMapping.objects d n)
    (r : Enriched.RightActionMapping.Relation (I := I)) :
    Enriched.RightActionMapping.familyLeft d (fun n => f ≫ q n) r =
      f ≫ Enriched.RightActionMapping.familyLeft d q r :=
  Enriched.RightActionMapping.familyLeft_precomp d f q r
end OrdinaryLeftRelations

section OrdinaryFullFamilies
universe vI
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  (d : Enriched.RightActionMapping.Data (V := V) (I := I))
  [HasProduct (Enriched.RightActionMapping.objects d)]
  [HasProduct (Enriched.RightActionMapping.relations d)]
  [HasEqualizer (Enriched.RightActionMapping.leftMap d)
    (Enriched.RightActionMapping.rightMap d)]

example {P : V} (app : ∀ n, P ⟶ Enriched.RightActionMapping.objects d n)
    (h : ∀ r, Enriched.RightActionMapping.familyLeft d app r =
      Enriched.RightActionMapping.familyRight d app r) :
    (Enriched.RightActionMapping.CompatibleFamily.mk app h).app = app := by rfl

example {P : V} (f : P ⟶ Enriched.RightActionMapping.Hom d) (n : I) :
    Enriched.RightActionMapping.CompatibleFamily.app
        (Enriched.RightActionMapping.representationEquiv d P f) n =
      f ≫ Enriched.RightActionMapping.π d n := by rfl

example {P : V} (q : Enriched.RightActionMapping.CompatibleFamily d P) :
    Enriched.RightActionMapping.representationEquiv d P
        ((Enriched.RightActionMapping.representationEquiv d P).symm q) = q :=
  (Enriched.RightActionMapping.representationEquiv d P).apply_symm_apply q
end OrdinaryFullFamilies

end CategoryTheory.RightActionAdjunctionOwner
