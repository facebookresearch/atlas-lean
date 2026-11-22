/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.StandardRightFree.Levels
import MathlibExt.CategoryTheory.Enriched.EnrichedAdjunctionFull
import MathlibExt.CategoryTheory.Enriched.EnrichedAdjunctionValue

/-!
# Enriched free evaluation for right symmetric modules

The free functor at a finite-bijection index and literal evaluation form an enriched
adjunction for right symmetric sphere modules. Its Hom object from a free coefficient X is
naturally the internal Hom from X into the evaluated module level. The formulas retain the
ordinary adjunct, unit, counit, points and their naturality maps.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.SymmetricActualRightFreeHom

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
  SymmetricModuleMappingComparison.literalEnrichedOrdinaryCategory

/-- The original right sphere modules with their literal mapping enrichment. -/
abbrev Carrier := SymmetricModuleMappingComparison.Carrier.{u, v}

/-- The original chosen standard RIGHT adjunction at its proved literal evaluation endpoint. -/
def adjunction (e : Operad.SmallFinBijGroupoid) :
    SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e ⊣
      SymmetricStandardRightFreeEvaluation.literalEvaluation.{u, v} e :=
  Adjunction.ofRightEq (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq e)
    (SymmetricStandardRightFreeEvaluation.originalAdjunction e)

/-- Actual whole free/evaluation Hom maps are derived from original levels and projections. -/
def data (e : Operad.SmallFinBijGroupoid) : EnrichedAdjunctionHom.Data
    (SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e)
    (SymmetricStandardRightFreeEvaluation.literalEvaluation.{u, v} e) where
  leftMap X Y := SymmetricScalarFunctorHom.homMap (OriginalStandardRightFreeLevels.data e) X Y
  rightMap M N := SymmetricRightModuleMapping.π M N e
  leftPoint f := SymmetricScalarFunctorHom.homMap_point (OriginalStandardRightFreeLevels.data e) f
  rightPoint f := SymmetricRightModuleMapping.homEquiv_π f e

/-- The original standard RIGHT free functor is genuinely enriched on the full Hom spaces. -/
def free (e : Operad.SmallFinBijGroupoid) :
    EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.{u, v} Carrier.{u, v} :=
  EnrichedAdjunctionHom.Full.leftFunctor (data e) isSeparator_tensorUnit

/-- Actual original evaluation is genuinely enriched by the full module mapping projection. -/
def evaluation (e : Operad.SmallFinBijGroupoid) :
    EnrichedFunctor PointedCGWH.{u, v} Carrier.{u, v} PointedCGWH.{u, v} :=
  EnrichedAdjunctionHom.Full.rightFunctor (data e) isSeparator_tensorUnit

/-- The actual original arbitrary-coefficient free/evaluation enriched Hom-object isomorphism. -/
def homIso (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v}) (M : Carrier.{u, v}) :
    ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X ⟶[PointedCGWH.{u, v}] M) ≅
      (ihom X).obj (M.X.functor.obj e) :=
  EnrichedAdjunctionHom.Full.homIso (data e) (adjunction e) isSeparator_tensorUnit X M

/-- The literal original continuous module mapping object evaluates to the original level. -/
def valueIso (e : Operad.SmallFinBijGroupoid) (M : Carrier.{u, v}) :
    ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj
      (𝟙_ PointedCGWH.{u, v}) ⟶[PointedCGWH.{u, v}] M) ≅ M.X.functor.obj e :=
  EnrichedAdjunctionHom.Full.valueIso (data e) (adjunction e) isSeparator_tensorUnit M

/-- Every actual original free Hom map retains its complete derived scalar parameter map. -/
theorem data_leftMap (e : Operad.SmallFinBijGroupoid) (X Y : PointedCGWH.{u, v}) :
    (data e).leftMap X Y =
      SymmetricScalarFunctorHom.homMap (OriginalStandardRightFreeLevels.data e) X Y := rfl

/-- Every actual original evaluation Hom map retains its complete original projection. -/
theorem data_rightMap (e : Operad.SmallFinBijGroupoid) (M N : Carrier.{u, v}) :
    (data e).rightMap M N = SymmetricRightModuleMapping.π M N e := rfl

/-- The entire original chosen unit map is preserved by the exact right-endpoint equality. -/
theorem adjunction_unit (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v}) :
    HEq ((adjunction e).unit.app X)
      ((SymmetricStandardRightFreeEvaluation.originalAdjunction e).unit.app X) :=
  Adjunction.ofRightEq_unit_app _ _ X

/-- The entire original chosen counit map is preserved by the exact right-endpoint equality. -/
theorem adjunction_counit (e : Operad.SmallFinBijGroupoid) (M : Carrier.{u, v}) :
    HEq ((adjunction e).counit.app M)
      ((SymmetricStandardRightFreeEvaluation.originalAdjunction e).counit.app M) :=
  Adjunction.ofRightEq_counit_app _ _ M

/-- Both entire original ordinary adjunct maps are preserved at every coefficient and module. -/
theorem adjunction_homEquiv (e : Operad.SmallFinBijGroupoid)
    (X : PointedCGWH.{u, v}) (M : Carrier.{u, v}) :
    HEq ((adjunction e).homEquiv X M)
      ((SymmetricStandardRightFreeEvaluation.originalAdjunction e).homEquiv X M) :=
  Adjunction.ofRightEq_homEquiv _ _ X M

/-- The original whole free/evaluation Hom correspondence is retained on all actual points. -/
theorem homIso_point (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v})
    (M : Carrier.{u, v})
    (f : (SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X ⟶ M) :
    eHomEquiv PointedCGWH.{u, v} f ≫ (homIso e X M).hom =
      eHomEquiv PointedCGWH.{u, v} ((adjunction e).homEquiv X M f) := by
  unfold homIso
  rw [EnrichedAdjunctionHom.Full.homIso_hom]
  exact EnrichedAdjunctionHom.Full.forward_point (data e) (adjunction e) X M f

/-- The entire original continuous value map is the actual original ordinary adjunct. -/
theorem valueIso_point (e : Operad.SmallFinBijGroupoid) (M : Carrier.{u, v})
    (f : (SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj
      (𝟙_ PointedCGWH.{u, v}) ⟶ M) :
    eHomEquiv PointedCGWH.{u, v} f ≫ (valueIso e M).hom =
      (adjunction e).homEquiv (𝟙_ PointedCGWH.{u, v}) M f :=
  EnrichedAdjunctionHom.UnitValue.valueIso_point (data e) (adjunction e) isSeparator_tensorUnit M f

/-- The entire original inverse value map is the actual original inverse adjunct. -/
theorem valueIso_inv_point (e : Operad.SmallFinBijGroupoid) (M : Carrier.{u, v})
    (f : 𝟙_ PointedCGWH.{u, v} ⟶ M.X.functor.obj e) :
    f ≫ (valueIso e M).inv =
      eHomEquiv PointedCGWH.{u, v}
        (((adjunction e).homEquiv (𝟙_ PointedCGWH.{u, v}) M).symm f) :=
  EnrichedAdjunctionHom.UnitValue.valueIso_inv_point (data e) (adjunction e)
    isSeparator_tensorUnit M f

/-- Both entire original continuous free/evaluation Hom maps are inverse. -/
theorem homIso_hom_inv (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v})
    (M : Carrier.{u, v}) : (homIso e X M).hom ≫ (homIso e X M).inv = 𝟙 _ :=
  (homIso e X M).hom_inv_id

/-- Both entire original continuous free/evaluation inverse Hom maps are inverse. -/
theorem homIso_inv_hom (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v})
    (M : Carrier.{u, v}) : (homIso e X M).inv ≫ (homIso e X M).hom = 𝟙 _ :=
  (homIso e X M).inv_hom_id

/-- Both entire original continuous value maps are inverse on the module mapping object. -/
theorem valueIso_hom_inv (e : Operad.SmallFinBijGroupoid) (M : Carrier.{u, v}) :
    (valueIso e M).hom ≫ (valueIso e M).inv = 𝟙 _ := (valueIso e M).hom_inv_id

/-- Both entire original continuous value maps are inverse on the original level. -/
theorem valueIso_inv_hom (e : Operad.SmallFinBijGroupoid) (M : Carrier.{u, v}) :
    (valueIso e M).inv ≫ (valueIso e M).hom = 𝟙 _ := (valueIso e M).inv_hom_id

/-- Every original parameter object is represented by the entire actual module mapping object. -/
def parameterEquiv (e : Operad.SmallFinBijGroupoid) (P X : PointedCGWH.{u, v})
    (M : Carrier.{u, v}) :
    (P ⟶ ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X ⟶[
      PointedCGWH.{u, v}] M)) ≃ (P ⟶ (ihom X).obj (M.X.functor.obj e)) :=
  EnrichedAdjunctionHom.Full.parameterEquiv (data e) (adjunction e) isSeparator_tensorUnit P X M

/-- Full original target naturality keeps both entire module-Hom parameters. -/
theorem target_naturality (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v})
    (M N : Carrier.{u, v}) :
    eComp PointedCGWH.{u, v}
      ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X) M N ≫
        (homIso e X N).hom =
          ((homIso e X M).hom ⊗ₘ (data e).rightMap M N) ≫
            eComp PointedCGWH.{u, v} X (M.X.functor.obj e) (N.X.functor.obj e) := by
  unfold homIso
  rw [EnrichedAdjunctionHom.Full.homIso_hom, EnrichedAdjunctionHom.Full.homIso_hom]
  exact EnrichedAdjunctionHom.Full.forward_target (data e) (adjunction e)
    isSeparator_tensorUnit X M N

/-- Full original source naturality keeps the entire coefficient and module-Hom parameters. -/
theorem source_naturality (e : Operad.SmallFinBijGroupoid) (X Y : PointedCGWH.{u, v})
    (M : Carrier.{u, v}) :
    let L := SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e
    ((data e).leftMap X Y ⊗ₘ 𝟙 (L.obj Y ⟶[PointedCGWH.{u, v}] M)) ≫
      eComp PointedCGWH.{u, v} (L.obj X) (L.obj Y) M ≫ (homIso e X M).hom =
        (𝟙 ((ihom X).obj Y) ⊗ₘ (homIso e Y M).hom) ≫
          eComp PointedCGWH.{u, v} X Y (M.X.functor.obj e) := by
  dsimp only
  unfold homIso
  rw [EnrichedAdjunctionHom.Full.homIso_hom, EnrichedAdjunctionHom.Full.homIso_hom]
  exact EnrichedAdjunctionHom.Full.forward_source (data e) (adjunction e)
    isSeparator_tensorUnit X Y M

/-- The entire original chosen standard RIGHT free unit and counit satisfy the enriched triangle. -/
theorem free_triangle (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v}) :
    let L := SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e
    let R := SymmetricStandardRightFreeEvaluation.literalEvaluation.{u, v} e
    (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
      ((eHomEquiv PointedCGWH.{u, v} ((adjunction e).unit.app X) ≫
        (data e).leftMap X (R.obj (L.obj X))) ⊗ₘ
          eHomEquiv PointedCGWH.{u, v} ((adjunction e).counit.app (L.obj X))) ≫
            eComp PointedCGWH.{u, v} (L.obj X) (L.obj (R.obj (L.obj X))) (L.obj X) =
              eId PointedCGWH.{u, v} (L.obj X) :=
  EnrichedAdjunctionHom.Full.left_triangle (data e) (adjunction e) X

/-- The original evaluation unit and counit satisfy the entire enriched triangle. -/
theorem evaluation_triangle (e : Operad.SmallFinBijGroupoid) (M : Carrier.{u, v}) :
    let L := SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e
    let R := SymmetricStandardRightFreeEvaluation.literalEvaluation.{u, v} e
    (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
      (eHomEquiv PointedCGWH.{u, v} ((adjunction e).unit.app (R.obj M)) ⊗ₘ
        (eHomEquiv PointedCGWH.{u, v} ((adjunction e).counit.app M) ≫
          (data e).rightMap (L.obj (R.obj M)) M)) ≫
            eComp PointedCGWH.{u, v} (R.obj M) (R.obj (L.obj (R.obj M))) (R.obj M) =
              eId PointedCGWH.{u, v} (R.obj M) :=
  EnrichedAdjunctionHom.Full.right_triangle (data e) (adjunction e) M

/-- Original continuous free mapping objects are naturally the actual original evaluation
functor. -/
def valueNatIso (e : Operad.SmallFinBijGroupoid) :
    eCoyoneda PointedCGWH.{u, v}
      ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj
        (𝟙_ PointedCGWH.{u, v})) ≅ SymmetricStandardRightFreeEvaluation.literalEvaluation e :=
  EnrichedAdjunctionHom.UnitValue.valueNatIso (data e) (adjunction e) isSeparator_tensorUnit

/-- The full Hom comparison is natural in every original target module. -/
def homNatIso (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v}) :
    eCoyoneda PointedCGWH.{u, v}
      ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X) ≅
        SymmetricStandardRightFreeEvaluation.literalEvaluation e ⋙ ihom X :=
  EnrichedAdjunctionHom.UnitValue.homNatIso (data e) (adjunction e) isSeparator_tensorUnit X

/-- The full Hom data uses the exact original evaluation functor endpoint. -/
def originalData (e : Operad.SmallFinBijGroupoid) : EnrichedAdjunctionHom.Data
    (SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e)
    (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v} e) := by
  rw [SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq]
  exact data e

/-- The original ordinary adjunction determines the full enriched Hom comparison. -/
def originalHomIso (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v})
    (M : Carrier.{u, v}) :
    ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X ⟶[
      PointedCGWH.{u, v}] M) ≅
        (ihom X).obj ((SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor e).obj M) :=
  EnrichedAdjunctionHom.Full.homIso (originalData e)
    (SymmetricStandardRightFreeEvaluation.originalAdjunction e) isSeparator_tensorUnit X M

/-- Both full original adjunct maps agree with the chosen ordinary adjunction on points. -/
theorem originalHomIso_point (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v})
    (M : Carrier.{u, v})
    (f : (SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X ⟶ M) :
    eHomEquiv PointedCGWH.{u, v} f ≫ (originalHomIso e X M).hom =
      eHomEquiv PointedCGWH.{u, v}
        ((SymmetricStandardRightFreeEvaluation.originalAdjunction e).homEquiv X M f) :=
  EnrichedAdjunctionHom.Full.forward_point (originalData e)
    (SymmetricStandardRightFreeEvaluation.originalAdjunction e) X M f

/-- The full inverse Hom map agrees with the exact original ordinary inverse adjunct. -/
theorem originalHomIso_inv_point (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v})
    (M : Carrier.{u, v})
    (f : X ⟶ (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor e).obj M) :
    eHomEquiv PointedCGWH.{u, v} f ≫ (originalHomIso e X M).inv =
      eHomEquiv PointedCGWH.{u, v}
        (((SymmetricStandardRightFreeEvaluation.originalAdjunction e).homEquiv X M).symm f) :=
  EnrichedAdjunctionHom.Full.inverse_point (originalData e)
    (SymmetricStandardRightFreeEvaluation.originalAdjunction e) X M f

/-- The full original Hom comparison is natural as a map of original module functors. -/
def originalHomNatIso (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v}) :
    eCoyoneda PointedCGWH.{u, v}
      ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X) ≅
        SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor e ⋙ ihom X :=
  EnrichedAdjunctionHom.UnitValue.homNatIso (originalData e)
    (SymmetricStandardRightFreeEvaluation.originalAdjunction e) isSeparator_tensorUnit X

/-- Mapping out of the original free unit is naturally the original evaluation functor. -/
def originalValueNatIso (e : Operad.SmallFinBijGroupoid) :
    eCoyoneda PointedCGWH.{u, v}
      ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj
        (𝟙_ PointedCGWH.{u, v})) ≅
          SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor e :=
  EnrichedAdjunctionHom.UnitValue.valueNatIso (originalData e)
    (SymmetricStandardRightFreeEvaluation.originalAdjunction e) isSeparator_tensorUnit

end PointedCGWH.SymmetricActualRightFreeHom
