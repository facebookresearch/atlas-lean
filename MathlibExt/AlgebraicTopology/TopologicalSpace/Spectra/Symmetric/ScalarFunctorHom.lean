/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModuleMappingComparison
public import MathlibExt.CategoryTheory.Enriched.MappingCompositionAlgebra

/-!
# Enriched Hom maps from scalar tensor levels

Suppose a functor to symmetric sphere modules has specified level isomorphisms L(X)ₙ ≅ X ⊗
Cₙ, natural in X. These data construct a compatible map from the internal Hom of X and Y to
the module Hom of L(X) and L(Y). Its level projections are the prescribed
tensor-and-transport maps, and its ordinary points are exactly the maps induced by L.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.SymmetricScalarFunctorHom

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
  SymmetricModuleMappingComparison.literalEnrichedOrdinaryCategory

/-- The symmetric right sphere modules with their literal mapping enrichment. -/
abbrev Carrier := SymmetricModuleMappingComparison.Carrier.{u, v}

/-- A whole actual scalar/free level isomorphism and its original ordinary naturality.
The desired mapping-object enrichment is not an input. -/
structure Data (L : PointedCGWH.{u, v} ⥤ Carrier.{u, v}) where
  /-- The coefficient object in each finite bijection degree. -/
  coefficient : Operad.SmallFinBijGroupoid → PointedCGWH.{u, v}
  /-- The level comparison with the tensor of the input and its coefficient. -/
  levelIso : ∀ X n, (L.obj X).X.functor.obj n ≅ X ⊗ coefficient n
  naturality : ∀ {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) n,
    (levelIso X n).hom ≫ (f ▷ coefficient n) =
      (L.map f).hom.natTrans.app n ≫ (levelIso Y n).hom

variable {L : PointedCGWH.{u, v} ⥤ Carrier.{u, v}} (d : Data L)

/-- Every complete parameter map uses the actual full tensor Hom map and level isomorphisms. -/
@[no_expose]
def componentMap (X Y : PointedCGWH.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    (ihom X).obj Y ⟶ (ihom ((L.obj X).X.functor.obj n)).obj ((L.obj Y).X.functor.obj n) :=
  (Enriched.SphereOperator.fixedRightTensor
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf PointedCGWH.{u, v})
    (d.coefficient n)).map X Y ≫
    eHomWhiskerRight PointedCGWH.{u, v} (d.levelIso X n).hom (Y ⊗ d.coefficient n) ≫
      eHomWhiskerLeft PointedCGWH.{u, v} ((L.obj X).X.functor.obj n) (d.levelIso Y n).inv

/-- Every ordinary scalar/free map is the original whole map at every complete unit point. -/
theorem componentMap_point {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (n : Operad.SmallFinBijGroupoid) :
    eHomEquiv PointedCGWH.{u, v} f ≫ componentMap d X Y n =
      eHomEquiv PointedCGWH.{u, v} ((L.map f).hom.natTrans.app n) := by
  let qX := (d.levelIso X n).hom
  let qY := (d.levelIso Y n).hom
  let qY' := (d.levelIso Y n).inv
  let f' := (L.map f).hom.natTrans.app n
  have hNat : qX ≫ (f ▷ d.coefficient n) = f' ≫ qY := d.naturality f n
  have hCancel : (qX ≫ (f ▷ d.coefficient n)) ≫ qY' = f' :=
    (congrArg (fun z => z ≫ qY') hNat).trans
      ((Category.assoc f' qY qY').trans
        ((congrArg (fun z => f' ≫ z) (d.levelIso Y n).hom_inv_id).trans (Category.comp_id f')))
  change eHomEquiv PointedCGWH.{u, v} f ≫
    (Enriched.SphereOperator.fixedRightTensor
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf PointedCGWH.{u, v})
      (d.coefficient n)).map X Y ≫
      eHomWhiskerRight PointedCGWH.{u, v} qX (Y ⊗ d.coefficient n) ≫
        eHomWhiskerLeft PointedCGWH.{u, v} ((L.obj X).X.functor.obj n) qY' = _
  let t : (ihom X).obj Y ⟶ (ihom (X ⊗ d.coefficient n)).obj (Y ⊗ d.coefficient n) :=
    (Enriched.SphereOperator.fixedRightTensor
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf PointedCGWH.{u, v})
      (d.coefficient n)).map X Y
  let pre := eHomWhiskerRight PointedCGWH.{u, v} qX (Y ⊗ d.coefficient n)
  let post := eHomWhiskerLeft PointedCGWH.{u, v} ((L.obj X).X.functor.obj n) qY'
  have tensorPoint := Enriched.SphereOperator.fixedRightTensor_point
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf PointedCGWH.{u, v}) (d.coefficient n) f
  simp only [Enriched.SphereOperator.fixedRightTensor_obj] at tensorPoint
  have prePoint := eHomEquiv_comp_eHomWhiskerRight
    PointedCGWH.{u, v} PointedCGWH.{u, v} qX (f ▷ d.coefficient n)
  have postPoint := eHomEquiv_comp_eHomWhiskerLeft
    PointedCGWH.{u, v} PointedCGWH.{u, v} (qX ≫ (f ▷ d.coefficient n)) qY'
  exact (Category.assoc (eHomEquiv PointedCGWH.{u, v} f) t (pre ≫ post)).symm.trans
    ((congrArg (fun z => z ≫ pre ≫ post) tensorPoint).trans
      ((Category.assoc (eHomEquiv PointedCGWH.{u, v} (f ▷ d.coefficient n)) pre post).symm.trans
        ((congrArg (fun z => z ≫ post) prePoint).trans
          (postPoint.trans (congrArg (eHomEquiv PointedCGWH.{u, v}) hCancel)))))

/-- All original degree/index/right-coefficient relations hold on the complete Hom parameter. -/
def family (X Y : PointedCGWH.{u, v}) :
    Enriched.RightActionMapping.CompatibleFamily
      (SymmetricRightModuleMapping.mappingData (L.obj X) (L.obj Y)) ((ihom X).obj Y) :=
  Enriched.RightActionMapping.familyOfPoints
    (SymmetricRightModuleMapping.mappingData (L.obj X) (L.obj Y)) ((ihom X).obj Y)
    (componentMap d X Y) isSeparator_tensorUnit (by
      intro p
      let f : X ⟶ Y := (eHomEquiv PointedCGWH.{u, v} (X := X) (Y := Y)).symm p
      refine ⟨SymmetricRightModuleMapping.toCompatibleHom (L.map f), ?_⟩
      intro n
      have hp : eHomEquiv PointedCGWH.{u, v} f = p :=
        (eHomEquiv PointedCGWH.{u, v} (X := X) (Y := Y)).apply_symm_apply p
      exact (congrArg (fun z => z ≫ componentMap d X Y n) hp).symm.trans
        (componentMap_point d f n))

/-- The actual continuous scalar/free Hom map lifts both complete original module relations. -/
@[no_expose]
def homMap (X Y : PointedCGWH.{u, v}) :
    (ihom X).obj Y ⟶ SymmetricRightModuleMapping.Hom (L.obj X) (L.obj Y) :=
  (SymmetricRightModuleMapping.parameterEquiv (L.obj X) (L.obj Y) ((ihom X).obj Y)).symm
    (family d X Y)

/-- Every whole mapping projection is the actual entire tensor parameter map. -/
@[reassoc]
theorem homMap_π (X Y : PointedCGWH.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    homMap d X Y ≫ SymmetricRightModuleMapping.π (L.obj X) (L.obj Y) n =
      componentMap d X Y n := by
  let e := SymmetricRightModuleMapping.parameterEquiv (L.obj X) (L.obj Y) ((ihom X).obj Y)
  exact (SymmetricRightModuleMapping.parameterEquiv_app (L.obj X) (L.obj Y) ((ihom X).obj Y)
    (e.symm (family d X Y)) n).symm.trans
      (congrArg (fun q => q.app n) (e.apply_symm_apply (family d X Y)))

/-- Every original ordinary scalar/free morphism is retained by the full Hom map. -/
theorem homMap_point {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    eHomEquiv PointedCGWH.{u, v} f ≫ homMap d X Y =
      SymmetricRightModuleMapping.homEquiv (L.obj X) (L.obj Y) (L.map f) := by
  apply (SymmetricRightModuleMapping.parameterEquiv (L.obj X) (L.obj Y)
    (𝟙_ PointedCGWH.{u, v})).injective
  apply Enriched.RightActionMapping.CompatibleFamily.ext
  funext n
  rw [SymmetricRightModuleMapping.parameterEquiv_app,
    SymmetricRightModuleMapping.parameterEquiv_app]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => eHomEquiv PointedCGWH.{u, v} f ≫ z) (homMap_π d X Y n)).trans
      ((componentMap_point d f n).trans (SymmetricRightModuleMapping.homEquiv_π (L.map f) n).symm))

end PointedCGWH.SymmetricScalarFunctorHom
