/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricScalarSmashCoefficient

/-!
# Coefficient naturality of the actual degree-zero scalar comparison

The entire original native free-function comparison and actual unit shift
retain the original coefficient pre-map and scalar cotensor map.
-/

set_option autoImplicit false
noncomputable section

universe uC vC u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.CoefficientPrimitive

variable {C : Type uC} [Category.{vC} C]

/-- An actual whole unit comparison removes the same source shift from
every target functor and every full coefficient natural transformation. -/
def removeUnitShift (S : C ⥤ C) (e : S ≅ 𝟭 C) (F : C ⥤ C) : S ⋙ F ≅ F :=
  Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F

/-- The entire unit-shift comparison retains coefficient naturality. -/
theorem removeUnitShift_coefficient (S : C ⥤ C) (e : S ≅ 𝟭 C)
    {F G : C ⥤ C} (q : F ⟶ G) :
    Functor.whiskerLeft S q ≫ (removeUnitShift S e G).hom =
      (removeUnitShift S e F).hom ≫ q := by
  apply NatTrans.ext
  funext X
  change q.app (S.obj X) ≫ (G.map (e.hom.app X) ≫ 𝟙 (G.obj X)) =
    (F.map (e.hom.app X) ≫ 𝟙 (F.obj X)) ≫ q.app X
  calc
    _ = q.app (S.obj X) ≫ G.map (e.hom.app X) :=
      congrArg (fun t => q.app (S.obj X) ≫ t) (Category.comp_id _)
    _ = F.map (e.hom.app X) ≫ q.app X := (q.naturality (e.hom.app X)).symm
    _ = _ :=
      congrArg (fun t => t ≫ q.app X) (Category.comp_id (F.map (e.hom.app X))).symm




end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.CoefficientPrimitive

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric

open NativeOmegaRecovery.NativeSymmetricFreeFunction

attribute [local irreducible] Mod.internalHom comparison

private def scalarUnitShift (T : V.{u, v}) :
    PointedCGWH.SymmetricShift.functor (𝟙_ I) ⋙ cotensor T ≅ cotensor T :=
  CoefficientPrimitive.removeUnitShift (PointedCGWH.SymmetricShift.functor (𝟙_ I))
    NativeOmegaRecovery.NativeSymmetricShiftUnit.comparison (cotensor T)

private theorem functionScalarIso_hom_factors (T : V.{u, v}) :
    (functionScalarIso T).hom =
      (nativeFreeComparison (𝟙_ I) T).hom ≫ (scalarUnitShift T).hom := rfl

private theorem scalarUnitShift_coefficient {T T' : V.{u, v}} (p : T ⟶ T') :
    Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor (𝟙_ I))
        ((ScalarLeibniz.cotensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p.op) ≫
      (scalarUnitShift T).hom =
    (scalarUnitShift T').hom ≫
      (ScalarLeibniz.cotensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p.op :=
  CoefficientPrimitive.removeUnitShift_coefficient
    (PointedCGWH.SymmetricShift.functor (𝟙_ I))
    NativeOmegaRecovery.NativeSymmetricShiftUnit.comparison
    ((ScalarLeibniz.cotensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p.op)

/-- Every original coefficient arrow preserves the actual degree-zero
function-spectrum/scalar-cotensor comparison. -/
theorem functionScalarIso_coefficient {T T' : V.{u, v}} (p : T ⟶ T') :
    NativeOmegaPreparation.NativeSymmetricFunction.precompose
        (Free.coefficientMap (PointedCGWH.symmetricOperatorObj (𝟙_ I)) p) ≫
      (functionScalarIso T).hom =
    (functionScalarIso T').hom ≫
      (ScalarLeibniz.cotensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p.op :=
  Primitive.pasteSquares (W := Carrier.{u, v} ⥤ Carrier.{u, v})
    (functionScalarIso_hom_factors T') (functionScalarIso_hom_factors T)
    (nativeFreeComparison_coefficient (𝟙_ I) p) (scalarUnitShift_coefficient p)





end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash
