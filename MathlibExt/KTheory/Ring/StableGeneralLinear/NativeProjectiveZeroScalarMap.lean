/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtension
public import MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentFunctor
public import MathlibExt.KTheory.Ring.K0.ComponentProduct
public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMap
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
public import MathlibExt.Topology.Category.TopCat.HomotopyExtension

/-!
# The original intrinsic six-role scalar map on native projective zero spaces

The functor first shrinks R, extends scalars, then shrinks and lifts S. Its
actual Pair functor is restricted through the original zero inclusion. The
canonical zero comparison is the SAME two-coordinate zeroPairIso, lifted
through that inclusion. It supplies a path, rather than a strict zero-object
identity. Actual vertex homotopy extension in the retained working lift
retunes the raw native chart map and records the whole canonical root trace.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SInverseS.ComponentTranslation
open scoped ContinuousMap Simplicial unitInterval

attribute [local instance] CategoryTheory.uliftCategory

namespace AlgebraicKTheory.StableGL

/-- The exact original shrink-R-first scalar functor, with independently
sized source and target projective modules. -/
public abbrev nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    FGProjectiveCat.{max uR uMR} R ⥤ FGProjectiveCat.{max uS uMS} S :=
  (FGProjectiveCat.universeEquivalence.{uR, uMR} R).functor ⋙
    FGProjectiveCat.scalarExtension.{uR, uS, uR} f ⋙
      (FGProjectiveCat.universeEquivalence.{uS, uR} S).functor ⋙
        (FGProjectiveCat.universeEquivalence.{uS, uMS} S).inverse

private theorem scalarOriginalFunctorAdditiveComputed.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f).Additive := by
  infer_instance

/-- Additivity is earned by the SAME original four functor factors. -/
public theorem nativeProjectiveZeroScalarFunctor_additive.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f).Additive :=
  scalarOriginalFunctorAdditiveComputed.{uR, uS, uMR, uMS} f

private theorem scalarOriginalFunctorExactComputed.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f).IsExact :=
  ExactCategory.isExact_splitSource _

/-- Exactness uses the original split exact projective source. -/
public theorem nativeProjectiveZeroScalarFunctor_isExact.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f).IsExact :=
  scalarOriginalFunctorExactComputed.{uR, uS, uMR, uMS} f

/-- Restrict the SAME Pair functor using its actual zero-component property. -/
public abbrev nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    SInverseS.ZeroComponent (C := FGProjectiveCat.{max uR uMR} R) ⥤
      SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S) :=
  SInverseS.zeroComponentFunctor (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)

private theorem scalarOriginalZeroObjectValueComputed.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (X : SInverseS.ZeroComponent (C := FGProjectiveCat.{max uR uMR} R)) :
    ((nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f).obj X).obj =
      (SInverseS.pairFunctor (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).obj
        X.obj :=
  SInverseS.zeroComponentFunctor_obj_obj
    (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) X

/-- Every restricted object retains the original Pair image, including F(0). -/
public theorem nativeProjectiveZeroScalarZeroFunctor_obj_obj.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (X : SInverseS.ZeroComponent (C := FGProjectiveCat.{max uR uMR} R)) :
    ((nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f).obj X).obj =
      (SInverseS.pairFunctor (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).obj
        X.obj :=
  scalarOriginalZeroObjectValueComputed.{uR, uS, uMR, uMS} f X

private def scalarOriginalZeroPointIsoComputed.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f).obj
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R)) ≅
      SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uS uMS} S) :=
  (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uMS} S)).isoMk
    (eqToIso (nativeProjectiveZeroScalarZeroFunctor_obj_obj.{uR, uS, uMR, uMS} f
      (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R))) ≪≫
        SInverseS.zeroPairIso (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f))

/-- The canonical zero-root Iso is the actual zeroPairIso through the full
original zero inclusion; no strict equality of selected zero objects is used. -/
public def nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f).obj
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R)) ≅
      SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uS uMS} S) :=
  scalarOriginalZeroPointIsoComputed.{uR, uS, uMR, uMS} f

private theorem scalarOriginalZeroPointIsoInclusionValueComputed.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uMS} S)).ι.mapIso
        (nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS} f) =
      eqToIso (nativeProjectiveZeroScalarZeroFunctor_obj_obj.{uR, uS, uMR, uMS} f
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R))) ≪≫
          SInverseS.zeroPairIso (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) := by
  apply Iso.ext
  rfl

/-- The whole inclusion value is the SAME canonical two-coordinate zeroPairIso. -/
public theorem nativeProjectiveZeroScalarZeroPointIso_inclusion_value.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uMS} S)).ι.mapIso
        (nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS} f) =
      eqToIso (nativeProjectiveZeroScalarZeroFunctor_obj_obj.{uR, uS, uMR, uMS} f
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R))) ≪≫
          SInverseS.zeroPairIso (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) :=
  scalarOriginalZeroPointIsoInclusionValueComputed.{uR, uS, uMR, uMS} f

/-- The raw ordinary map realizes the SAME actual restricted functor. -/
public def ordinaryProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    C(zeroSpace (C := FGProjectiveCat.{max uR uMR} R),
      zeroSpace (C := FGProjectiveCat.{max uS uMS} S)) :=
  CategoryTheory.realizedNerveFunctorMap
    (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)

/-- The raw native map transports through the SAME original realization Isos,
with source and target native realization roles independently retained. -/
public def nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    C(RingK0.projectiveZeroSpace.{uR, uMR, uNR} R,
      RingK0.projectiveZeroSpace.{uS, uMS, uNS} S) :=
  (nativeZeroRealizationIso.{((max uS uMS) + 1), max uS uMS, uNS}
    (C := FGProjectiveCat.{max uS uMS} S)).inv.hom.comp
      ((ordinaryProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS} f).comp
        (nativeZeroRealizationIso.{((max uR uMR) + 1), max uR uMR, uNR}
          (C := FGProjectiveCat.{max uR uMR} R)).hom.hom)

private theorem scalarOriginalNativeRawValueComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f =
      (nativeZeroRealizationIso.{((max uS uMS) + 1), max uS uMS, uNS}
        (C := FGProjectiveCat.{max uS uMS} S)).inv.hom.comp
          ((CategoryTheory.realizedNerveFunctorMap
            (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)).comp
              (nativeZeroRealizationIso.{((max uR uMR) + 1), max uR uMR, uNR}
                (C := FGProjectiveCat.{max uR uMR} R)).hom.hom) := by
  rfl

/-- The entire raw map has the literal original mixed-world chart value. -/
public theorem nativeProjectiveZeroScalarRawMap_value.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f =
      (nativeZeroRealizationIso.{((max uS uMS) + 1), max uS uMS, uNS}
        (C := FGProjectiveCat.{max uS uMS} S)).inv.hom.comp
          ((CategoryTheory.realizedNerveFunctorMap
            (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)).comp
              (nativeZeroRealizationIso.{((max uR uMR) + 1), max uR uMR, uNR}
                (C := FGProjectiveCat.{max uR uMR} R)).hom.hom) :=
  scalarOriginalNativeRawValueComputed.{uR, uS, uMR, uMS, uNR, uNS} f

private theorem scalarOriginalNativeRawRealizationComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeZeroRealizationIso.{((max uS uMS) + 1), max uS uMS, uNS}
        (C := FGProjectiveCat.{max uS uMS} S)).hom.hom.comp
      (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f) =
      (ordinaryProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS} f).comp
        (nativeZeroRealizationIso.{((max uR uMR) + 1), max uR uMR, uNR}
          (C := FGProjectiveCat.{max uR uMR} R)).hom.hom := by
  apply ContinuousMap.ext
  intro x
  exact TopCat.inv_hom_id_apply
    (nativeZeroRealizationIso.{((max uS uMS) + 1), max uS uMS, uNS}
      (C := FGProjectiveCat.{max uS uMS} S))
    (ordinaryProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS} f
      ((nativeZeroRealizationIso.{((max uR uMR) + 1), max uR uMR, uNR}
        (C := FGProjectiveCat.{max uR uMR} R)).hom x))

/-- The whole raw native-to-ordinary square follows from the SAME chart inverse law. -/
public theorem nativeProjectiveZeroScalarRawMap_realization.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeZeroRealizationIso.{((max uS uMS) + 1), max uS uMS, uNS}
        (C := FGProjectiveCat.{max uS uMS} S)).hom.hom.comp
      (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f) =
      (ordinaryProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS} f).comp
        (nativeZeroRealizationIso.{((max uR uMR) + 1), max uR uMR, uNR}
          (C := FGProjectiveCat.{max uR uMR} R)).hom.hom :=
  scalarOriginalNativeRawRealizationComputed.{uR, uS, uMR, uMS, uNR, uNS} f

private abbrev scalarOriginalWorkingSourceCategory.{uR, uS, uMR, uMS, uNR, uNS}
    (R : Type uR) [Ring R] :=
  ULiftHom.{max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS} (ULift.{max ((max uR uMR) + 1) ((max
      uS uMS) + 1) uNR uNS}
    (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uR uMR} R)))

private abbrev scalarOriginalWorkingTargetCategory.{uR, uS, uMR, uMS, uNR, uNS}
    (S : Type uS) [Ring S] :=
  ULiftHom.{max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS} (ULift.{max ((max uR uMR) + 1) ((max
      uS uMS) + 1) uNR uNS}
    (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S)))

private abbrev scalarOriginalWorkingSourceSpace.{uR, uS, uMR, uMS, uNR, uNS}
    (R : Type uR) [Ring R] : TopCat.{max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS} :=
  SSet.toTop.obj (nerve (scalarOriginalWorkingSourceCategory.{uR, uS, uMR, uMS, uNR, uNS} R))

private abbrev scalarOriginalWorkingTargetSpace.{uR, uS, uMR, uMS, uNR, uNS}
    (S : Type uS) [Ring S] : TopCat.{max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS} :=
  SSet.toTop.obj (nerve (scalarOriginalWorkingTargetCategory.{uR, uS, uMR, uMS, uNR, uNS} S))

private def scalarOriginalWorkingSourcePoint.{uR, uS, uMR, uMS, uNR, uNS}
    (R : Type uR) [Ring R] : scalarOriginalWorkingSourceSpace.{uR, uS, uMR, uMS, uNR, uNS} R :=
  SSet.realizedVertex
    (X := nerve (scalarOriginalWorkingSourceCategory.{uR, uS, uMR, uMS, uNR, uNS} R))
    (ComposableArrows.mk₀ (ULiftHom.objUp (ULift.up
      (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R)))))

private def scalarOriginalWorkingTargetPoint.{uR, uS, uMR, uMS, uNR, uNS}
    (S : Type uS) [Ring S] : scalarOriginalWorkingTargetSpace.{uR, uS, uMR, uMS, uNR, uNS} S :=
  SSet.realizedVertex
    (X := nerve (scalarOriginalWorkingTargetCategory.{uR, uS, uMR, uMS, uNR, uNS} S))
    (ComposableArrows.mk₀ (ULiftHom.objUp (ULift.up
      (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uS uMS} S)))))

private abbrev scalarOriginalWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    scalarOriginalWorkingSourceCategory.{uR, uS, uMR, uMS, uNR, uNS} R ⥤
      scalarOriginalWorkingTargetCategory.{uR, uS, uMR, uMS, uNR, uNS} S :=
  (ULiftHomULiftCategory.equiv.{max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS, max ((max uR uMR)
      + 1) ((max uS uMS) + 1) uNR uNS, ((max uR uMR) + 1), ((max uR uMR) + 1)}
    (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uR uMR} R))).inverse ⋙
      nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f ⋙
        (ULiftHomULiftCategory.equiv.{max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS, max ((max
            uR uMR) + 1) ((max uS uMS) + 1) uNR uNS, ((max uS uMS) + 1), ((max uS uMS) + 1)}
          (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S))).functor

private abbrev scalarOriginalWorkingRawMap.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    C(scalarOriginalWorkingSourceSpace.{uR, uS, uMR, uMS, uNR, uNS} R,
      scalarOriginalWorkingTargetSpace.{uR, uS, uMR, uMS, uNR, uNS} S) :=
  (SSet.toTop.map (nerveMap (scalarOriginalWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f))).hom

private abbrev scalarOriginalWorkingZeroPointIso.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  (ULiftHomULiftCategory.equiv.{max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS, max ((max uR uMR)
      + 1) ((max uS uMS) + 1) uNR uNS, ((max uS uMS) + 1), ((max uS uMS) + 1)}
    (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S))).functor.mapIso
      (nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS} f)

private theorem scalarOriginalWorkingRawPointComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    scalarOriginalWorkingRawMap.{uR, uS, uMR, uMS, uNR, uNS} f
        (scalarOriginalWorkingSourcePoint.{uR, uS, uMR, uMS, uNR, uNS} R) =
      SSet.realizedVertex
        (X := nerve (scalarOriginalWorkingTargetCategory.{uR, uS, uMR, uMS, uNR, uNS} S))
        (ComposableArrows.mk₀ ((ULiftHomULiftCategory.equiv.{max ((max uR uMR) + 1) ((max uS uMS) +
            1) uNR uNS, max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS, ((max uS uMS) + 1), ((max
            uS uMS) + 1)}
          (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S))).functor.obj
          ((nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f).obj
            (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R))))) := by
  let z : scalarOriginalWorkingSourceCategory.{uR, uS, uMR, uMS, uNR, uNS} R :=
    ULiftHom.objUp (ULift.up
      (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R)))
  have h := (SSet.realizedVertex_naturality
    (nerveMap (scalarOriginalWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f))
    (ComposableArrows.mk₀ z)).symm
  exact h.trans (congrArg
    (SSet.realizedVertex
      (X := nerve (scalarOriginalWorkingTargetCategory.{uR, uS, uMR, uMS, uNR, uNS} S)))
    (nerveMap_app_mk₀ (scalarOriginalWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f) z))

private def scalarOriginalWorkingRootPath.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (scalarOriginalWorkingRawMap.{uR, uS, uMR, uMS, uNR, uNS} f
      (scalarOriginalWorkingSourcePoint.{uR, uS, uMR, uMS, uNR, uNS} R))
      (scalarOriginalWorkingTargetPoint.{uR, uS, uMR, uMS, uNR, uNS} S) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk
    (scalarOriginalWorkingZeroPointIso.{uR, uS, uMR, uMS, uNR, uNS} f).hom))).cast
      (scalarOriginalWorkingRawPointComputed.{uR, uS, uMR, uMS, uNR, uNS} f) rfl

private def scalarOriginalNativeSourceToWorking.{uR, uS, uMR, uMS, uNR, uNS}
    (R : Type uR) [Ring R] :
    C(RingK0.projectiveZeroSpace.{uR, uMR, uNR} R,
      scalarOriginalWorkingSourceSpace.{uR, uS, uMR, uMS, uNR, uNS} R) :=
  (SSet.realizedNerveLiftHomeomorph.{((max uR uMR) + 1), ((max uR uMR) + 1), max ((max uR uMR) + 1)
      ((max uS uMS) + 1) uNR uNS}
    (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uR uMR} R))).symm.toHomotopyEquiv.toFun.comp
      (nativeZeroRealizationIso.{((max uR uMR) + 1), max uR uMR, uNR}
        (C := FGProjectiveCat.{max uR uMR} R)).hom.hom

private def scalarOriginalWorkingTargetToNative.{uR, uS, uMR, uMS, uNR, uNS}
    (S : Type uS) [Ring S] :
    C(scalarOriginalWorkingTargetSpace.{uR, uS, uMR, uMS, uNR, uNS} S,
      RingK0.projectiveZeroSpace.{uS, uMS, uNS} S) :=
  (nativeZeroRealizationIso.{((max uS uMS) + 1), max uS uMS, uNS}
    (C := FGProjectiveCat.{max uS uMS} S)).inv.hom.comp
      (SSet.realizedNerveLiftHomeomorph.{((max uS uMS) + 1), ((max uS uMS) + 1), max ((max uR uMR) +
          1) ((max uS uMS) + 1) uNR uNS}
        (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S))).toHomotopyEquiv.toFun

private theorem scalarOriginalSourceWorkingPointComputed.{uR, uS, uMR, uMS, uNR, uNS}
    (R : Type uR) [Ring R] :
    scalarOriginalNativeSourceToWorking.{uR, uS, uMR, uMS, uNR, uNS} R
        (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) =
      scalarOriginalWorkingSourcePoint.{uR, uS, uMR, uMS, uNR, uNS} R := by
  let nativeSourceIso := nativeZeroRealizationIso.{((max uR uMR) + 1), max uR uMR, uNR}
    (C := FGProjectiveCat.{max uR uMR} R)
  let H := SSet.realizedNerveLiftHomeomorph.{((max uR uMR) + 1), ((max uR uMR) + 1), max ((max uR
      uMR) + 1) ((max uS uMS) + 1) uNR uNS}
    (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uR uMR} R))
  have hI : nativeSourceIso.hom (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) =
      zeroSpacePoint (C := FGProjectiveCat.{max uR uMR} R) :=
    (congrArg nativeSourceIso.hom (RingK0.projectiveZeroPoint_eq_native.{uR, uMR, uNR} R)).trans
      (nativeZeroRealizationIso_point.{((max uR uMR) + 1), max uR uMR, uNR}
        (C := FGProjectiveCat.{max uR uMR} R))
  exact (congrArg H.symm hI).trans
    ((congrArg H.symm (zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.{max uR uMR} R))).trans
      (SSet.realizedNerveLiftHomeomorph_symm_vertex.{((max uR uMR) + 1), ((max uR uMR) + 1), max
          ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS}
        (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uR uMR} R))
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R))))

private theorem scalarOriginalTargetNativePointComputed.{uR, uS, uMR, uMS, uNR, uNS}
    (S : Type uS) [Ring S] :
    scalarOriginalWorkingTargetToNative.{uR, uS, uMR, uMS, uNR, uNS} S
        (scalarOriginalWorkingTargetPoint.{uR, uS, uMR, uMS, uNR, uNS} S) =
      RingK0.projectiveZeroPoint.{uS, uMS, uNS} S := by
  let nativeTargetIso := nativeZeroRealizationIso.{((max uS uMS) + 1), max uS uMS, uNS}
    (C := FGProjectiveCat.{max uS uMS} S)
  have hH := (SSet.realizedNerveLiftHomeomorph_vertex.{((max uS uMS) + 1), ((max uS uMS) + 1), max
      ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS}
    (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S))
    (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uS uMS} S))).trans
      (zeroSpacePoint_eq_realizedVertex (C := FGProjectiveCat.{max uS uMS} S)).symm
  exact (congrArg nativeTargetIso.inv hH).trans
    ((nativeZeroRealizationIso_inv_point.{((max uS uMS) + 1), max uS uMS, uNS}
      (C := FGProjectiveCat.{max uS uMS} S)).trans
        (RingK0.projectiveZeroPoint_eq_native.{uS, uMS, uNS} S).symm)

private theorem scalarOriginalNativeRawWorkingRecipeComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f =
      (scalarOriginalWorkingTargetToNative.{uR, uS, uMR, uMS, uNR, uNS} S).comp
        ((scalarOriginalWorkingRawMap.{uR, uS, uMR, uMS, uNR, uNS} f).comp
          (scalarOriginalNativeSourceToWorking.{uR, uS, uMR, uMS, uNR, uNS} R)) := by
  have hRecipe := CategoryTheory.realizedNerveFunctorMap_larger_recipe.{((max uR uMR) + 1), ((max uR
      uMR) + 1), ((max uS uMS) + 1), ((max uS uMS) + 1), max uNR uNS}
    (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)
  apply ContinuousMap.ext
  intro x
  exact congrArg
    (nativeZeroRealizationIso.{((max uS uMS) + 1), max uS uMS, uNS}
      (C := FGProjectiveCat.{max uS uMS} S)).inv
    (congrArg (fun q : C(zeroSpace (C := FGProjectiveCat.{max uR uMR} R),
      zeroSpace (C := FGProjectiveCat.{max uS uMS} S)) =>
        q ((nativeZeroRealizationIso.{((max uR uMR) + 1), max uR uMR, uNR}
          (C := FGProjectiveCat.{max uR uMR} R)).hom x)) hRecipe)

private theorem scalarOriginalNativeRawWorkingRootPointComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f
        (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) =
      scalarOriginalWorkingTargetToNative.{uR, uS, uMR, uMS, uNR, uNS} S
        (scalarOriginalWorkingRawMap.{uR, uS, uMR, uMS, uNR, uNS} f
          (scalarOriginalWorkingSourcePoint.{uR, uS, uMR, uMS, uNR, uNS} R)) :=
  (congrArg
    (fun q : C(RingK0.projectiveZeroSpace.{uR, uMR, uNR} R,
      RingK0.projectiveZeroSpace.{uS, uMS, uNS} S) =>
        q (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R))
    (scalarOriginalNativeRawWorkingRecipeComputed.{uR, uS, uMR, uMS, uNR, uNS} f)).trans
    (congrArg (fun z => scalarOriginalWorkingTargetToNative.{uR, uS, uMR, uMS, uNR, uNS} S
      (scalarOriginalWorkingRawMap.{uR, uS, uMR, uMS, uNR, uNS} f z))
      (scalarOriginalSourceWorkingPointComputed.{uR, uS, uMR, uMS, uNR, uNS} R))

private def scalarOriginalNativeRootPathComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  ((scalarOriginalWorkingRootPath.{uR, uS, uMR, uMS, uNR, uNS} f).map
    (scalarOriginalWorkingTargetToNative.{uR, uS, uMR, uMS, uNR, uNS} S).continuous).cast
      (scalarOriginalNativeRawWorkingRootPointComputed.{uR, uS, uMR, uMS, uNR, uNS} f)
      (scalarOriginalTargetNativePointComputed.{uR, uS, uMR, uMS, uNR, uNS} S).symm

/-- The native zero-root path is the SAME actual zeroPairIso edge in the
retained working lift, transported through the original target chart. -/
public def nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  scalarOriginalNativeRootPathComputed.{uR, uS, uMR, uMS, uNR, uNS} f

private theorem scalarOriginalNativeRootClockValueComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f t =
      (nativeZeroRealizationIso.{((max uS uMS) + 1), max uS uMS, uNS}
        (C := FGProjectiveCat.{max uS uMS} S)).inv
        ((SSet.realizedNerveLiftHomeomorph.{((max uS uMS) + 1), ((max uS uMS) + 1), max ((max uR
            uMR) + 1) ((max uS uMS) + 1) uNR uNS}
          (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S)))
          ((TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk
            ((ULiftHomULiftCategory.equiv.{max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS, max
                ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS, ((max uS uMS) + 1), ((max uS uMS) +
                1)}
              (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S))).functor.mapIso
              (nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS} f)).hom))) t)) := by
  rfl

/-- Every time keeps the SAME actual lifted zeroPairIso edge and native chart value. -/
public theorem nativeProjectiveZeroScalarRawRootPath_value.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f t =
      (nativeZeroRealizationIso.{((max uS uMS) + 1), max uS uMS, uNS}
        (C := FGProjectiveCat.{max uS uMS} S)).inv
        ((SSet.realizedNerveLiftHomeomorph.{((max uS uMS) + 1), ((max uS uMS) + 1), max ((max uR
            uMR) + 1) ((max uS uMS) + 1) uNR uNS}
          (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S)))
          ((TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk
            ((ULiftHomULiftCategory.equiv.{max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS, max
                ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS, ((max uS uMS) + 1), ((max uS uMS) +
                1)}
              (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S))).functor.mapIso
              (nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS} f)).hom))) t)) :=
  scalarOriginalNativeRootClockValueComputed.{uR, uS, uMR, uMS, uNR, uNS} f t

private abbrev scalarOriginalWorkingPointMap.{uR, uS, uMR, uMS, uNR, uNS}
    (R : Type uR) [Ring R] :
    C(PUnit.{max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS + 1},
        scalarOriginalWorkingSourceSpace.{uR, uS, uMR, uMS, uNR, uNS} R) :=
  ContinuousMap.const _ (scalarOriginalWorkingSourcePoint.{uR, uS, uMR, uMS, uNR, uNS} R)

private def scalarOriginalWorkingExtensionData.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Topology.HomotopyExtensionData
      (scalarOriginalWorkingPointMap.{uR, uS, uMR, uMS, uNR, uNS} R)
      (scalarOriginalWorkingRawMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      ((scalarOriginalWorkingRootPath.{uR, uS, uMR, uMS, uNR, uNS} f).toContinuousMap.comp
        ContinuousMap.fst)
      (fun _ => (scalarOriginalWorkingRootPath.{uR, uS, uMR, uMS, uNR, uNS} f).source) := by
  have hHEP : Topology.HasHomotopyExtensionProperty.{max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR
      uNS, max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS}
      (scalarOriginalWorkingPointMap.{uR, uS, uMR, uMS, uNR, uNS} R) :=
    SSet.realizedVertex_isHurewiczCofibration
      (X := nerve (scalarOriginalWorkingSourceCategory.{uR, uS, uMR, uMS, uNR, uNS} R))
      (ComposableArrows.mk₀ (ULiftHom.objUp (ULift.up
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R)))))
  exact Classical.choice (hHEP
    (scalarOriginalWorkingRawMap.{uR, uS, uMR, uMS, uNR, uNS} f)
    ((scalarOriginalWorkingRootPath.{uR, uS, uMR, uMS, uNR, uNS} f).toContinuousMap.comp
      ContinuousMap.fst)
    (fun _ => (scalarOriginalWorkingRootPath.{uR, uS, uMR, uMS, uNR, uNS} f).source))

private def scalarOriginalNativeBasedMapComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    C(RingK0.projectiveZeroSpace.{uR, uMR, uNR} R,
      RingK0.projectiveZeroSpace.{uS, uMS, uNS} S) :=
  (scalarOriginalWorkingTargetToNative.{uR, uS, uMR, uMS, uNR, uNS} S).comp
    ((scalarOriginalWorkingExtensionData.{uR, uS, uMR, uMS, uNR, uNS} f).endpoint.comp
      (scalarOriginalNativeSourceToWorking.{uR, uS, uMR, uMS, uNR, uNS} R))

/-- The intrinsic based scalar map is the actual vertex-HEP endpoint of the
SAME raw map/root path. It is independent of all plus-normalization choices. -/
public def nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    C(RingK0.projectiveZeroSpace.{uR, uMR, uNR} R,
      RingK0.projectiveZeroSpace.{uS, uMS, uNS} S) :=
  scalarOriginalNativeBasedMapComputed.{uR, uS, uMR, uMS, uNR, uNS} f

private theorem scalarOriginalNativeBasedPointComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f
        (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) =
      RingK0.projectiveZeroPoint.{uS, uMS, uNS} S := by
  let d := scalarOriginalWorkingExtensionData.{uR, uS, uMR, uMS, uNR, uNS} f
  let b := scalarOriginalWorkingTargetToNative.{uR, uS, uMR, uMS, uNR, uNS} S
  change b (d.endpoint (scalarOriginalNativeSourceToWorking.{uR, uS, uMR, uMS, uNR, uNS} R
    (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R))) = _
  rw [scalarOriginalSourceWorkingPointComputed.{uR, uS, uMR, uMS, uNR, uNS} R]
  exact (congrArg b (d.extension_subspace 1 (PUnit.unit : PUnit.{max ((max uR uMR) + 1) ((max uS
      uMS) + 1) uNR uNS + 1}))).trans
    ((congrArg b (scalarOriginalWorkingRootPath.{uR, uS, uMR, uMS, uNR, uNS} f).target).trans
      (scalarOriginalTargetNativePointComputed.{uR, uS, uMR, uMS, uNR, uNS} S))

/-- The strict native-zero point law is derived from extension_subspace at 1
and the SAME canonical root-path target, rather than component membership. -/
public theorem nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f
        (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) =
      RingK0.projectiveZeroPoint.{uS, uMS, uNS} S :=
  scalarOriginalNativeBasedPointComputed.{uR, uS, uMR, uMS, uNR, uNS} f

private def scalarOriginalNativeRetuningComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy
      (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f) :=
  ((ContinuousMap.Homotopy.refl
    (scalarOriginalWorkingTargetToNative.{uR, uS, uMR, uMS, uNR, uNS} S)).comp
      ((scalarOriginalWorkingExtensionData.{uR, uS, uMR, uMS, uNR, uNS}
          f).toHomotopy.compContinuousMap (scalarOriginalNativeSourceToWorking.{uR, uS, uMR, uMS,
          uNR, uNS} R))).cast
          (scalarOriginalNativeRawWorkingRecipeComputed.{uR, uS, uMR, uMS, uNR, uNS} f).symm rfl

/-- The SAME whole raw-to-based homotopy transports the actual chosen HEP data
through the original source and target working charts. -/
public def nativeProjectiveZeroScalarRetuning.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy
      (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f) :=
  scalarOriginalNativeRetuningComputed.{uR, uS, uMR, uMS, uNR, uNS} f

/-- The complete intrinsic raw-to-based continuous family, with no extra choice. -/
public def nativeProjectiveZeroScalarRetuningFamily.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    C(unitInterval × RingK0.projectiveZeroSpace.{uR, uMR, uNR} R,
      RingK0.projectiveZeroSpace.{uS, uMS, uNS} S) :=
  (nativeProjectiveZeroScalarRetuning.{uR, uS, uMR, uMS, uNR, uNS} f).toContinuousMap

private theorem scalarOriginalNativeRetuningFamilyValueComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarRetuning.{uR, uS, uMR, uMS, uNR, uNS} f).toContinuousMap =
      nativeProjectiveZeroScalarRetuningFamily.{uR, uS, uMR, uMS, uNR, uNS} f := by
  rfl

/-- The retuning retains the entire SAME continuous-family value. -/
public theorem nativeProjectiveZeroScalarRetuning_toContinuousMap.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarRetuning.{uR, uS, uMR, uMS, uNR, uNS} f).toContinuousMap =
      nativeProjectiveZeroScalarRetuningFamily.{uR, uS, uMR, uMS, uNR, uNS} f :=
  scalarOriginalNativeRetuningFamilyValueComputed.{uR, uS, uMR, uMS, uNR, uNS} f

private theorem scalarOriginalNativeRetuningRootComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarRetuningFamily.{uR, uS, uMR, uMS, uNR, uNS} f
        (t, RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) =
      nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f t := by
  let d := scalarOriginalWorkingExtensionData.{uR, uS, uMR, uMS, uNR, uNS} f
  let b := scalarOriginalWorkingTargetToNative.{uR, uS, uMR, uMS, uNR, uNS} S
  change b (d.extension (t,
    scalarOriginalNativeSourceToWorking.{uR, uS, uMR, uMS, uNR, uNS} R
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R))) =
    b (scalarOriginalWorkingRootPath.{uR, uS, uMR, uMS, uNR, uNS} f t)
  rw [scalarOriginalSourceWorkingPointComputed.{uR, uS, uMR, uMS, uNR, uNS} R]
  exact congrArg b (d.extension_subspace t (PUnit.unit : PUnit.{max ((max uR uMR) + 1) ((max uS uMS)
      + 1) uNR uNS + 1}))

/-- Every interval time retains the actual canonical zeroPairIso root path,
including the same original working-lift and native chart clocks. -/
public theorem nativeProjectiveZeroScalarRetuningFamily_root_value.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarRetuningFamily.{uR, uS, uMR, uMS, uNR, uNS} f
        (t, RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) =
      nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f t :=
  scalarOriginalNativeRetuningRootComputed.{uR, uS, uMR, uMS, uNR, uNS} f t

private theorem scalarOriginalNativeRetuningRootPathComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ((nativeProjectiveZeroScalarRetuning.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)).cast rfl
        (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f).symm =
      nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f := by
  apply Path.ext
  funext t
  exact scalarOriginalNativeRetuningRootComputed.{uR, uS, uMR, uMS, uNR, uNS} f t

/-- The entire endpoint-fixed root trace is the SAME original canonical path;
only the internally derived endpoint point law supplies its target cast. -/
public theorem nativeProjectiveZeroScalarRetuning_root_path.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ((nativeProjectiveZeroScalarRetuning.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)).cast rfl
        (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f).symm =
      nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f :=
  scalarOriginalNativeRetuningRootPathComputed.{uR, uS, uMR, uMS, uNR, uNS} f

end AlgebraicKTheory.StableGL

end
