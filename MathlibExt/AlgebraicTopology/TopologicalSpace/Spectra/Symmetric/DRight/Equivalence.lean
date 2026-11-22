/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.DRight.Point
import MathlibExt.CategoryTheory.Enriched.HomIsoEquivalence
import MathlibExt.CategoryTheory.Enriched.RestrictionInversePair

/-!
# Symmetric modules and the right-source index category

Constructs inverse enriched functors between the right-source index category and the symmetric operator index, using the full enriched Hom isomorphisms. Their restriction equivalence compares sphere modules with right-source diagrams and retains unit, counit, triangle, level and morphism-component formulas.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.SymmetricDRightEquivalence

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
  SymmetricModuleMappingComparison.literalEnrichedOrdinaryCategory

/-- The entire original standard RIGHT module carrier of the source equivalence. -/
abbrev Carrier := SymmetricModuleMappingComparison.Carrier.{u, v}
open SymmetricDRightHomComparison

private theorem identityProof (d : SymmetricDRight.Index) :
    eId PointedCGWH.{u, v} d ≫ (fullHomIso.{u, v} d d).hom =
      eId PointedCGWH.{u, v} (objectEquiv.{u, v} d) :=
  SymmetricDRightPoint.homIso_identity d.asIndex

private theorem compositionProof (d e k : SymmetricDRight.Index) :
    eComp PointedCGWH.{u, v} d e k ≫ (fullHomIso.{u, v} d k).hom =
      ((fullHomIso.{u, v} d e).hom ⊗ₘ (fullHomIso.{u, v} e k).hom) ≫
        eComp PointedCGWH.{u, v} (objectEquiv.{u, v} d)
          (objectEquiv.{u, v} e) (objectEquiv.{u, v} k) :=
  SymmetricDRightPoint.homIso_composition d.asIndex e.asIndex k.asIndex

/-- The independent original module mapping category maps on every full native coend Hom. -/
def sourceToOperator : EnrichedFunctor PointedCGWH.{u, v}
    SymmetricDRight.Index SymmetricOperatorIndex.{u, v} :=
  EnrichedHomIsoEquivalence.forward objectEquiv fullHomIso identityProof compositionProof

/-- The complete inverse coend map recovers the actual original module mapping category. -/
def operatorToSource : EnrichedFunctor PointedCGWH.{u, v}
    SymmetricOperatorIndex.{u, v} SymmetricDRight.Index :=
  EnrichedHomIsoEquivalence.inverse objectEquiv fullHomIso identityProof compositionProof

/-- Both entire enriched Hom maps recover the original D_R identity functor. -/
theorem source_inverse : sourceToOperator.{u, v}.comp PointedCGWH.{u, v}
    operatorToSource.{u, v} = EnrichedFunctor.id PointedCGWH.{u, v} SymmetricDRight.Index :=
  EnrichedHomIsoEquivalence.forward_inverse objectEquiv fullHomIso identityProof compositionProof

/-- Both complete inverse maps recover the full original J identity functor. -/
theorem operator_inverse : operatorToSource.{u, v}.comp PointedCGWH.{u, v}
    sourceToOperator.{u, v} =
      EnrichedFunctor.id PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} :=
  EnrichedHomIsoEquivalence.inverse_forward objectEquiv fullHomIso identityProof compositionProof

/-- Whole genuine source diagrams have actual inverse full-Hom restriction functors. -/
def diagramEquivalence : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricDRight.Index ≌
    EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} :=
  EnrichedFunctorCat.RestrictionInversePair.diagramEquivalence sourceToOperator operatorToSource
    source_inverse operator_inverse

/-- The actual original source diagrams retain their entire natural unit. -/
def unitNatIso : 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} SymmetricDRight.Index) ≅
    EnrichedFunctorCat.restriction operatorToSource ⋙
      EnrichedFunctorCat.restriction sourceToOperator :=
  EnrichedFunctorCat.RestrictionInversePair.unitNatIso sourceToOperator operatorToSource
    source_inverse

/-- The actual full J diagrams retain the entire natural counit. -/
def counitNatIso : EnrichedFunctorCat.restriction sourceToOperator ⋙
    EnrichedFunctorCat.restriction operatorToSource ≅
      𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}) :=
  EnrichedFunctorCat.RestrictionInversePair.counitNatIso sourceToOperator operatorToSource
    operator_inverse

section WholeTriangles
universe uV vV uA uB
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]

private theorem source_triangle_of_actual_isos
    (F : EnrichedFunctor V A B) (G : EnrichedFunctor V B A)
    (hFG : F.comp V G = EnrichedFunctor.id V A)
    (hGF : G.comp V F = EnrichedFunctor.id V B)
    (i : 𝟭 (EnrichedFunctorCat V A) ≅
      EnrichedFunctorCat.restriction G ⋙ EnrichedFunctorCat.restriction F)
    (j : EnrichedFunctorCat.restriction F ⋙ EnrichedFunctorCat.restriction G ≅
      𝟭 (EnrichedFunctorCat V B))
    (hi : i = EnrichedFunctorCat.RestrictionInversePair.unitNatIso F G hFG)
    (hj : j = EnrichedFunctorCat.RestrictionInversePair.counitNatIso F G hGF)
    (X : EnrichedFunctorCat V A) :
    (EnrichedFunctorCat.restriction G).map (i.hom.app X) ≫
      j.hom.app ((EnrichedFunctorCat.restriction G).obj X) = 𝟙 _ := by
  rw [hi, hj]
  exact EnrichedFunctorCat.RestrictionInversePair.source_triangle F G hFG hGF X

private theorem target_triangle_of_actual_isos
    (F : EnrichedFunctor V A B) (G : EnrichedFunctor V B A)
    (hFG : F.comp V G = EnrichedFunctor.id V A)
    (hGF : G.comp V F = EnrichedFunctor.id V B)
    (i : 𝟭 (EnrichedFunctorCat V A) ≅
      EnrichedFunctorCat.restriction G ⋙ EnrichedFunctorCat.restriction F)
    (j : EnrichedFunctorCat.restriction F ⋙ EnrichedFunctorCat.restriction G ≅
      𝟭 (EnrichedFunctorCat V B))
    (hi : i = EnrichedFunctorCat.RestrictionInversePair.unitNatIso F G hFG)
    (hj : j = EnrichedFunctorCat.RestrictionInversePair.counitNatIso F G hGF)
    (X : EnrichedFunctorCat V B) :
    i.hom.app ((EnrichedFunctorCat.restriction F).obj X) ≫
      (EnrichedFunctorCat.restriction F).map (j.hom.app X) = 𝟙 _ := by
  rw [hi, hj]
  exact EnrichedFunctorCat.RestrictionInversePair.target_triangle F G hFG hGF X
end WholeTriangles

/-- The original source restriction and complete unit/counit satisfy the first triangle. -/
theorem source_triangle
    (X : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricDRight.Index) :
    (EnrichedFunctorCat.restriction operatorToSource).map (unitNatIso.hom.app X) ≫
      counitNatIso.hom.app ((EnrichedFunctorCat.restriction operatorToSource).obj X) = 𝟙 _ :=
  source_triangle_of_actual_isos sourceToOperator operatorToSource
    source_inverse operator_inverse unitNatIso counitNatIso rfl rfl X

/-- The full original J restriction satisfies the other complete triangle. -/
theorem operator_triangle
    (X : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}) :
    unitNatIso.hom.app ((EnrichedFunctorCat.restriction sourceToOperator).obj X) ≫
      (EnrichedFunctorCat.restriction sourceToOperator).map (counitNatIso.hom.app X) = 𝟙 _ :=
  target_triangle_of_actual_isos sourceToOperator operatorToSource
    source_inverse operator_inverse unitNatIso counitNatIso rfl rfl X

/-- Every actual original standard RIGHT module has its whole original source diagram. -/
def moduleToSource : Carrier.{u, v} ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} SymmetricDRight.Index :=
  SymmetricRightModulePresentation.rightModuleToOperator ⋙
    EnrichedFunctorCat.restriction sourceToOperator

/-- Every genuine original source diagram recovers the whole original standard RIGHT module. -/
def sourceToModule : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricDRight.Index ⥤
    Carrier.{u, v} :=
  EnrichedFunctorCat.restriction operatorToSource ⋙
    SymmetricRightModulePresentation.operatorToRightModule

/-- The actual original standard RIGHT modules and independent D_R source diagrams are
equivalent. -/
def moduleDiagramEquivalence : Carrier.{u, v} ≌
    EnrichedFunctorCat PointedCGWH.{u, v} SymmetricDRight.Index :=
  SymmetricRightModulePresentation.rightModuleOperatorEquivalence.trans diagramEquivalence.symm

/-- Each entire forward source object is its actual original degree label. -/
theorem sourceToOperator_obj (d : SymmetricDRight.Index) :
    sourceToOperator.{u, v}.obj d = objectEquiv.{u, v} d :=
  EnrichedHomIsoEquivalence.forward_obj objectEquiv fullHomIso identityProof compositionProof d

/-- Every full forward Hom map is the actual original module/coend isomorphism map. -/
theorem sourceToOperator_map (d e : SymmetricDRight.Index) :
    HEq (sourceToOperator.{u, v}.map d e) (fullHomIso.{u, v} d e).hom :=
  EnrichedHomIsoEquivalence.forward_map objectEquiv fullHomIso identityProof compositionProof d e

/-- Each inverse operator object has its actual original source label. -/
theorem operatorToSource_obj (d : SymmetricOperatorIndex.{u, v}) :
    operatorToSource.{u, v}.obj d = objectEquiv.{u, v}.symm d :=
  EnrichedHomIsoEquivalence.inverse_obj objectEquiv fullHomIso identityProof compositionProof d

/-- The entire inverse Hom map retains both object equalities and the full original inverse. -/
theorem operatorToSource_map (d e : SymmetricOperatorIndex.{u, v}) :
    HEq (operatorToSource.{u, v}.map d e)
      (EnrichedHomIsoEquivalence.inverseMap objectEquiv fullHomIso d e) :=
  EnrichedHomIsoEquivalence.inverse_map objectEquiv fullHomIso identityProof compositionProof d e

/-- The complete original module carrier functor is the actual full source restriction. -/
theorem moduleDiagram_functor :
    moduleDiagramEquivalence.{u, v}.functor = moduleToSource.{u, v} := by
  unfold moduleDiagramEquivalence moduleToSource diagramEquivalence
  change SymmetricRightModulePresentation.rightModuleToOperator ⋙
    (EnrichedFunctorCat.RestrictionInversePair.diagramEquivalence sourceToOperator
      operatorToSource source_inverse operator_inverse).inverse = _
  rw [EnrichedFunctorCat.RestrictionInversePair.equivalence_inverse]

/-- The complete original inverse module carrier is the actual whole inverse source restriction. -/
theorem moduleDiagram_inverse :
    moduleDiagramEquivalence.{u, v}.inverse = sourceToModule.{u, v} := by
  unfold moduleDiagramEquivalence sourceToModule diagramEquivalence
  change (EnrichedFunctorCat.RestrictionInversePair.diagramEquivalence sourceToOperator
    operatorToSource source_inverse operator_inverse).functor ⋙
      SymmetricRightModulePresentation.operatorToRightModule = _
  rw [EnrichedFunctorCat.RestrictionInversePair.equivalence_functor]

/-- The actual original module unit and counit satisfy the entire forward triangle. -/
theorem module_triangle (M : Carrier.{u, v}) :
    moduleDiagramEquivalence.functor.map (moduleDiagramEquivalence.unitIso.hom.app M) ≫
      moduleDiagramEquivalence.counitIso.hom.app (moduleDiagramEquivalence.functor.obj M) = 𝟙 _ :=
  moduleDiagramEquivalence.functor_unitIso_comp M

/-- The actual source unit and counit satisfy the whole inverse module triangle. -/
theorem moduleSource_triangle
    (X : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricDRight.Index) :
    moduleDiagramEquivalence.unitIso.hom.app (moduleDiagramEquivalence.inverse.obj X) ≫
      moduleDiagramEquivalence.inverse.map (moduleDiagramEquivalence.counitIso.hom.app X) = 𝟙 _ :=
  moduleDiagramEquivalence.unit_inverse_comp X

/-- Every actual source degree retains the original entire module level. -/
theorem moduleToSource_level (M : Carrier.{u, v}) (d : Operad.SmallFinBijGroupoid) :
    (moduleToSource.obj M).toEnrichedFunctor.obj (SymmetricDRight.obj d) =
      M.X.functor.obj d := by
  change (SymmetricRightModulePresentation.rightModuleToOperator.obj M).toEnrichedFunctor.obj
    (sourceToOperator.obj (SymmetricDRight.obj d)) = _
  rw [sourceToOperator_obj, objectEquiv_apply,
    SymmetricRightModulePresentation.rightModuleToOperator_obj]

universe uA

private theorem component_index_heq {A : Type uA} [EnrichedCategory PointedCGWH.{u, v} A]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (t : X ⟶ Y) {a b : A} (h : a = b) :
    HEq (EnrichedFunctorCat.component t a) (EnrichedFunctorCat.component t b) := by
  cases h
  rfl

/-- Every complete original module morphism retains its original sequence component. -/
theorem moduleToSource_component {M N : Carrier.{u, v}} (f : M ⟶ N)
    (d : Operad.SmallFinBijGroupoid) :
    HEq (EnrichedFunctorCat.component (moduleToSource.map f) (SymmetricDRight.obj d))
      (f.hom.natTrans.app d) := by
  change HEq (EnrichedFunctorCat.component (EnrichedFunctorCat.restrictionMap sourceToOperator
    (SymmetricRightModulePresentation.rightModuleToOperator.map f)) (SymmetricDRight.obj d)) _
  have hcomponent := EnrichedFunctorCat.restrictionMap_component sourceToOperator
    (SymmetricRightModulePresentation.rightModuleToOperator.map f) (SymmetricDRight.obj d)
  have hindex := (sourceToOperator_obj (SymmetricDRight.obj d)).trans (objectEquiv_apply d)
  exact (heq_of_eq hcomponent).trans
    ((component_index_heq (SymmetricRightModulePresentation.rightModuleToOperator.map f)
      hindex).trans
        (heq_of_eq (SymmetricRightModulePresentation.rightModuleToOperator_component f d)))

/-- The actual underlying original sequences and all their original index arrows. -/
def underlyingSequence : Carrier.{u, v} ⥤
    (Operad.SmallFinBijGroupoid ⥤ PointedCGWH.{u, v}) where
  obj M := M.X.functor
  map f := f.hom.natTrans
  map_id M := by rfl
  map_comp f g := by rfl

/-- The original entire sequence unit isomorphism comes from the actual original module unit. -/
def originalSequenceUnitIso (M : Carrier.{u, v}) :
    M.X.functor ≅
      (moduleDiagramEquivalence.inverse.obj (moduleDiagramEquivalence.functor.obj M)).X.functor :=
  underlyingSequence.mapIso (moduleDiagramEquivalence.unitIso.app M)

/-- The inverse original sequence unit retains the same complete original module inverse. -/
theorem originalSequenceUnitIso_hom (M : Carrier.{u, v}) :
    (originalSequenceUnitIso M).hom = (moduleDiagramEquivalence.unitIso.hom.app M).hom.natTrans :=
  rfl

/-- The entire original sequence inverse is the actual original inverse module unit. -/
theorem originalSequenceUnitIso_inv (M : Carrier.{u, v}) :
    (originalSequenceUnitIso M).inv = (moduleDiagramEquivalence.unitIso.inv.app M).hom.natTrans :=
  rfl

/-- The complete original sequence unit retains both actual module inverse laws. -/
theorem originalSequenceUnitIso_hom_inv (M : Carrier.{u, v}) :
    (originalSequenceUnitIso M).hom ≫ (originalSequenceUnitIso M).inv = 𝟙 _ :=
  (originalSequenceUnitIso M).hom_inv_id

/-- The full original sequence retraction retains the original other inverse law. -/
theorem originalSequenceUnitIso_inv_hom (M : Carrier.{u, v}) :
    (originalSequenceUnitIso M).inv ≫ (originalSequenceUnitIso M).hom = 𝟙 _ :=
  (originalSequenceUnitIso M).inv_hom_id

end PointedCGWH.SymmetricDRightEquivalence
