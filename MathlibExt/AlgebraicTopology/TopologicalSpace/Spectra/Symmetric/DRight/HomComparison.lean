/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.DRight.FreeHom
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.DRightOrdinary
import MathlibExt.CategoryTheory.Enriched.Ordinary.HomCongr
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.StandardRightFree.Source
import MathlibExt.CategoryTheory.Enriched.FreeMappingSource

/-!
# Enriched Hom comparison for the right-module source

The enriched Hom in `SymmetricDRight` is identified with the mapping object
between its free right modules in reverse order. The free/evaluation
comparison gives `homIso` to the native symmetric-operator Hom object,
including both inverse maps. A degree-label bijection and `sourceFunctor`
describe the object and ordinary-point formulas through free Yoneda evaluation.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.SymmetricDRightHomComparison

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
  SymmetricModuleMappingComparison.literalEnrichedOrdinaryCategory

/-- The original standard RIGHT carrier for the entire free Hom comparison. -/
abbrev Carrier := SymmetricModuleMappingComparison.Carrier.{u, v}

/-- The original free object is the literal actual original standard RIGHT free value. -/
def freeObjectIso (e : Operad.SmallFinBijGroupoid) :
    SymmetricDRight.freeObject.{u, v} e ≅
      (SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj
        (𝟙_ PointedCGWH.{u, v}) :=
  eqToIso (SymmetricDRight.freeObject_eq e)

/-- Original D_R Hom is the entire actual original enriched module mapping object. -/
def sourceHomIso (d e : Operad.SmallFinBijGroupoid) :
    (SymmetricDRight.obj d ⟶[PointedCGWH.{u, v}] SymmetricDRight.obj e) ≅
      (SymmetricDRight.freeObject e ⟶[PointedCGWH.{u, v}] SymmetricDRight.freeObject d) :=
  eqToIso ((SymmetricDRight.Hom_eq d e).trans
    (SymmetricModuleMappingComparison.literalHom_eq
      (SymmetricDRight.freeObject e) (SymmetricDRight.freeObject d)).symm)

/-- The actual source-Hom initializer retains the full original ordinary module point. -/
theorem sourceHomIso_point (d e : Operad.SmallFinBijGroupoid)
    (f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) :
    eHomEquiv PointedCGWH.{u, v} f ≫ (sourceHomIso d e).hom =
      eHomEquiv PointedCGWH.{u, v} (C := Carrier.{u, v})
        (SymmetricDRightOrdinary.homEquiv d e f) :=
  SymmetricDRightOrdinary.original_enrichment_chosen_iso_point d e
    ((SymmetricDRight.Hom_eq d e).trans
      (SymmetricModuleMappingComparison.literalHom_eq
        (SymmetricDRight.freeObject e) (SymmetricDRight.freeObject d)).symm)
    (sourceHomIso d e) rfl f

/-- The independent literal original D_R mapping object is the whole native J coend Hom. -/
def homIso (d e : Operad.SmallFinBijGroupoid) :
    (SymmetricDRight.obj d ⟶[PointedCGWH.{u, v}] SymmetricDRight.obj e) ≅
      (symmetricOperatorObj.{u, v} d ⟶[PointedCGWH.{u, v}] symmetricOperatorObj.{u, v} e) :=
  sourceHomIso d e ≪≫
    Iso.eHomCongr PointedCGWH.{u, v} (freeObjectIso e)
      (Iso.refl (SymmetricDRight.freeObject d)) ≪≫
      SymmetricActualRightFreeHom.valueIso e (SymmetricDRight.freeObject d) ≪≫
        (SymmetricStandardRightFreeEvaluation.literalEvaluation e).mapIso (freeObjectIso d) ≪≫
          OriginalStandardRightFreeLevels.levelIso d (𝟙_ PointedCGWH.{u, v}) e ≪≫
            (λ_ (OriginalStandardRightFreeLevels.coefficient d e))

/-- The full original continuous D_R and coend maps are inverse. -/
theorem homIso_hom_inv (d e : Operad.SmallFinBijGroupoid) :
    (homIso.{u, v} d e).hom ≫ (homIso.{u, v} d e).inv = 𝟙 _ := by
  exact Iso.hom_inv_id (homIso.{u, v} d e)

/-- The full original continuous inverse coend and D_R maps are inverse. -/
theorem homIso_inv_hom (d e : Operad.SmallFinBijGroupoid) :
    (homIso.{u, v} d e).inv ≫ (homIso.{u, v} d e).hom =
      𝟙 (OriginalStandardRightFreeLevels.coefficient.{u, v} d e) := by
  exact Iso.inv_hom_id (homIso.{u, v} d e)

/-- The whole original free object is compared on every full J action by the same actual counit. -/
def operatorFreeIso (d : Operad.SmallFinBijGroupoid) :
    SymmetricRightModulePresentation.rightModuleToOperator.obj
      (SymmetricDRight.freeObject.{u, v} d) ≅
        EnrichedFunctorCat.Free.object (symmetricOperatorObj.{u, v} d)
          (𝟙_ PointedCGWH.{u, v}) :=
  SymmetricRightModulePresentation.rightModuleToOperator.mapIso (freeObjectIso d) ≪≫
    (OriginalStandardRightFreeLevels.originalOperatorFreeIso d).app (𝟙_ PointedCGWH.{u, v})

/-- All original opposite free-module arrows form a genuine comparison functor. -/
def sourceFunctor : SymmetricDRight.Index ⥤
    ForgetEnrichment PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} :=
  EnrichedFunctorCat.FreeMappingSource.functor
    (fun d : SymmetricDRight.Index => symmetricOperatorObj.{u, v} d.asIndex)
    (fun d : SymmetricDRight.Index => SymmetricDRight.freeObject.{u, v} d.asIndex)
    SymmetricRightModulePresentation.rightModuleToOperator
    (fun d => operatorFreeIso d.asIndex)

/-- The entire original source map is free evaluation after the whole carrier comparison. -/
theorem sourceFunctor_map (d e : Operad.SmallFinBijGroupoid)
    (f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) :
    HEq (sourceFunctor.{u, v}.map f)
      (ForgetEnrichment.homOf PointedCGWH.{u, v}
        (EnrichedFunctorCat.FreeYoneda.evaluateHom
          (symmetricOperatorObj.{u, v} d) (symmetricOperatorObj.{u, v} e)
          ((operatorFreeIso e).inv ≫
            SymmetricRightModulePresentation.rightModuleToOperator.map f.hom.unop ≫
              (operatorFreeIso d).hom))) := by
  exact EnrichedFunctorCat.FreeMappingSource.functor_map _ _ _ _ f

/-- The actual independent D_R and native J objects have their original degree-label bijection. -/
def objectEquiv : SymmetricDRight.Index ≃ SymmetricOperatorIndex.{u, v} where
  toFun d := symmetricOperatorObj d.asIndex
  invFun j := SymmetricDRight.obj (ForgetEnrichment.to PointedCGWH.{u, v}
    (C := CopowerIndex.{u, v, 0} Operad.SmallFinBijGroupoid) j.asIndex)
  left_inv d := by cases d; rfl
  right_inv j := by cases j; rfl

/-- Every actual original source degree is sent to the literal native operator object. -/
theorem objectEquiv_apply (d : Operad.SmallFinBijGroupoid) :
    objectEquiv.{u, v} (SymmetricDRight.obj d) = symmetricOperatorObj.{u, v} d := rfl

/-- Every actual native degree returns to the same independent original source object. -/
theorem objectEquiv_symm_apply (d : Operad.SmallFinBijGroupoid) :
    objectEquiv.{u, v}.symm (symmetricOperatorObj.{u, v} d) = SymmetricDRight.obj d := rfl

/-- All full source Hom objects compare at every actual degree, without a restricted subcarrier. -/
def fullHomIso (d e : SymmetricDRight.Index) :
    (d ⟶[PointedCGWH.{u, v}] e) ≅
      (objectEquiv.{u, v} d ⟶[PointedCGWH.{u, v}] objectEquiv.{u, v} e) :=
  homIso d.asIndex e.asIndex

/-- Every literal source pair retains the exact whole original Hom isomorphism. -/
theorem fullHomIso_obj (d e : Operad.SmallFinBijGroupoid) :
    fullHomIso.{u, v} (SymmetricDRight.obj d) (SymmetricDRight.obj e) =
      homIso.{u, v} d e := rfl

/-- The actual source functor retains its original literal degree objects. -/
theorem sourceFunctor_object (d : SymmetricDRight.Index) :
    sourceFunctor.{u, v}.obj d =
      ForgetEnrichment.of PointedCGWH.{u, v} (objectEquiv.{u, v} d) :=
  EnrichedFunctorCat.FreeMappingSource.functor_obj
    (fun d : SymmetricDRight.Index => symmetricOperatorObj.{u, v} d.asIndex)
    (fun d : SymmetricDRight.Index => SymmetricDRight.freeObject.{u, v} d.asIndex)
    SymmetricRightModulePresentation.rightModuleToOperator
    (fun d => operatorFreeIso d.asIndex) d

/-- Every source arrow retains its full original free point and object transport. -/
theorem sourceFunctor_point (d e : Operad.SmallFinBijGroupoid)
    (f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) :
    ForgetEnrichment.homTo PointedCGWH.{u, v} (sourceFunctor.{u, v}.map f) ≫
      eqToHom (congrArg₂
        (fun P Q : ForgetEnrichment PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} =>
          (ForgetEnrichment.to PointedCGWH.{u, v} P ⟶[PointedCGWH.{u, v}]
            ForgetEnrichment.to PointedCGWH.{u, v} Q))
              (sourceFunctor_object (SymmetricDRight.obj d))
              (sourceFunctor_object (SymmetricDRight.obj e))) =
        EnrichedFunctorCat.FreeYoneda.evaluateHom
          (symmetricOperatorObj.{u, v} d) (symmetricOperatorObj.{u, v} e)
          ((operatorFreeIso e).inv ≫
            SymmetricRightModulePresentation.rightModuleToOperator.map f.hom.unop ≫
              (operatorFreeIso d).hom) := by
  exact EnrichedFunctorCat.FreeMappingSource.functor_point_rebased
    (fun d : SymmetricDRight.Index => symmetricOperatorObj.{u, v} d.asIndex)
    (fun d : SymmetricDRight.Index => SymmetricDRight.freeObject.{u, v} d.asIndex)
    SymmetricRightModulePresentation.rightModuleToOperator
    (fun d => operatorFreeIso d.asIndex) f

end PointedCGWH.SymmetricDRightHomComparison
