/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.NativeProjectiveZeroScalarMap
public import MathlibExt.Algebra.Category.FGProjectiveCat.CategoryUniverseLift
public import MathlibExt.KTheory.Exact.Quillen.Equivalence
public import MathlibExt.KTheory.Exact.Quillen.ZeroCoherence

/-!
# Actual mixed Q-category lifts and their canonical zero-root square

The original projective categories are lifted by the existing separate
object/Hom universe equivalences into a common working frame. Descent,
the SAME intrinsic scalar functor and the original target lift define the
working functor. The original lift equivalence unit derives its whole
categorical square. QuillenQ.map and its actual zero-comparison Isos
retain the two chosen zeros without asserting their strict equality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_additive
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_isExact

namespace AlgebraicKTheory.StableGL

/-- The actual original R projectives lifted in the shared object/Hom frame. -/
public abbrev mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} (R : Type uR) [Ring R] :
  Type (max (max uR uMR + 1) (max uS uMS + 1) uNR uNS) :=
  FGProjectiveCat.CategoryUniverseLift.category.{uR, uMR, max (max uR uMR + 1) (max uS uMS + 1)
    uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R

/-- The same actual object/Hom lift of original S projectives in that frame. -/
public abbrev mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} (S : Type uS) [Ring S] :
  Type (max (max uR uMR + 1) (max uS uMS + 1) uNR uNS) :=
  FGProjectiveCat.CategoryUniverseLift.category.{uS, uMS, max (max uR uMR + 1) (max uS uMS + 1)
    uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S

/-- The working functor is actual source descent, ORIGINAL F and target lift. -/
public abbrev mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R ⥤
      mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S :=
  FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uMR, max (max uR uMR + 1) (max uS uMS + 1)
    uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R ⋙
    nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f ⋙
      FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS, max (max uR uMR + 1) (max uS uMS +
        1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S

private def originalProjectiveLiftSquareComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS uMS + 1)
      uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R ⋙
        mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f ≅
      nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f ⋙
        FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS, max (max uR uMR + 1) (max uS uMS
          + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S := by
  let E := FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uMR, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let A := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S
  exact (Functor.associator E.functor E.inverse (F ⋙ A)).symm ≪≫
    Functor.isoWhiskerRight E.unitIso.symm (F ⋙ A) ≪≫ Functor.leftUnitor (F ⋙ A)

/-- The original source lift unit derives the whole actual scalar lift square. -/
public def mixedOriginalProjectiveLiftSquare.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS uMS + 1)
      uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R ⋙
        mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f ≅
      nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f ⋙
        FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS, max (max uR uMR + 1) (max uS uMS
          + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S :=
  originalProjectiveLiftSquareComputed.{uR, uS, uMR, uMS, uNR, uNS} f

/-- BOTH actual source Q-equivalence directions are induced by original up/down. -/
public def mixedOriginalQUniverseEquivalenceR.{uR, uS, uMR, uMS, uNR, uNS} (R : Type uR) [Ring R] :
    QuillenQ (FGProjectiveCat.{max uR uMR} R) ≌
      QuillenQ (mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R) := by
  let E := FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uMR, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R
  let _ : E.functor.Additive :=
    FGProjectiveCat.CategoryUniverseLift.upFunctorAdditive.{uR, uMR, max (max uR uMR + 1) (max uS
      uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R
  let _ : E.inverse.Additive :=
    FGProjectiveCat.CategoryUniverseLift.downFunctorAdditive.{uR, uMR, max (max uR uMR + 1) (max
      uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R
  let _ : E.functor.IsExact :=
    FGProjectiveCat.CategoryUniverseLift.upFunctorIsExact.{uR, uMR, max (max uR uMR + 1) (max uS
      uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R
  let _ : E.inverse.IsExact :=
    FGProjectiveCat.CategoryUniverseLift.downFunctorIsExact.{uR, uMR, max (max uR uMR + 1) (max uS
      uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R
  exact QuillenQ.equivOfEquivalence E

/-- BOTH actual target Q-equivalence directions are the same canonical lifts. -/
public def mixedOriginalQUniverseEquivalenceS.{uR, uS, uMR, uMS, uNR, uNS} (S : Type uS) [Ring S] :
    QuillenQ (FGProjectiveCat.{max uS uMS} S) ≌
      QuillenQ (mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S) := by
  let E := FGProjectiveCat.CategoryUniverseLift.equivalence.{uS, uMS, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S
  let _ : E.functor.Additive :=
    FGProjectiveCat.CategoryUniverseLift.upFunctorAdditive.{uS, uMS, max (max uR uMR + 1) (max uS
      uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S
  let _ : E.inverse.Additive :=
    FGProjectiveCat.CategoryUniverseLift.downFunctorAdditive.{uS, uMS, max (max uR uMR + 1) (max
      uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S
  let _ : E.functor.IsExact :=
    FGProjectiveCat.CategoryUniverseLift.upFunctorIsExact.{uS, uMS, max (max uR uMR + 1) (max uS
      uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S
  let _ : E.inverse.IsExact :=
    FGProjectiveCat.CategoryUniverseLift.downFunctorIsExact.{uS, uMS, max (max uR uMR + 1) (max uS
      uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S
  exact QuillenQ.equivOfEquivalence E

/-- The full source equivalence forward functor has its original Q.map value. -/
public theorem mixedOriginalQUniverseEquivalenceR_forward.{uR, uS, uMR, uMS, uNR, uNS} (R : Type
  uR) [Ring R] :
    (mixedOriginalQUniverseEquivalenceR.{uR, uS, uMR, uMS, uNR, uNS} R).functor =
      QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{
        uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR
          uNS} R) := by
  rfl

/-- The full source equivalence inverse retains its original Q.map descent. -/
public theorem mixedOriginalQUniverseEquivalenceR_inverse.{uR, uS, uMR, uMS, uNR, uNS} (R : Type
  uR) [Ring R] :
    (mixedOriginalQUniverseEquivalenceR.{uR, uS, uMR, uMS, uNR, uNS} R).inverse =
      QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{
        uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR
          uNS} R) := by
  rfl

/-- The full target equivalence forward functor is its original Q.map lift. -/
public theorem mixedOriginalQUniverseEquivalenceS_forward.{uR, uS, uMR, uMS, uNR, uNS} (S : Type
  uS) [Ring S] :
    (mixedOriginalQUniverseEquivalenceS.{uR, uS, uMR, uMS, uNR, uNS} S).functor =
      QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{
        uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR
          uNS} S) := by
  rfl

/-- The full target equivalence inverse is the original Q.map descent. -/
public theorem mixedOriginalQUniverseEquivalenceS_inverse.{uR, uS, uMR, uMS, uNR, uNS} (S : Type
  uS) [Ring S] :
    (mixedOriginalQUniverseEquivalenceS.{uR, uS, uMR, uMS, uNR, uNS} S).inverse =
      QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{
        uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR
          uNS} S) := by
  rfl

/-- The mapped original R zero is compared to the actual chosen working zero. -/
public def mixedOriginalQUpZeroIsoR.{uR, uS, uMR, uMS, uNR, uNS} (R : Type uR) [Ring R] :
    (QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{
      uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR
        uNS} R)).obj (⟨0⟩ : QuillenQ (FGProjectiveCat.{max uR uMR} R)) ≅
      (⟨0⟩ : QuillenQ (mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R)) :=
  QuillenQ.zeroComparisonIso
    (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS uMS +
      1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R)

/-- The actual chosen working R zero has its canonical original descent root. -/
public def mixedOriginalQDownZeroIsoR.{uR, uS, uMR, uMS, uNR, uNS} (R : Type uR) [Ring R] :
    (QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{
      uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR
        uNS} R)).obj
      (⟨0⟩ : QuillenQ (mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R)) ≅
      (⟨0⟩ : QuillenQ (FGProjectiveCat.{max uR uMR} R)) :=
  QuillenQ.zeroComparisonIso
    (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uMR, max (max uR uMR + 1) (max uS uMS +
      1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R)

/-- The original S zero is compared through the same target working lift. -/
public def mixedOriginalQUpZeroIsoS.{uR, uS, uMR, uMS, uNR, uNS} (S : Type uS) [Ring S] :
    (QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{
      uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR
        uNS} S)).obj (⟨0⟩ : QuillenQ (FGProjectiveCat.{max uS uMS} S)) ≅
      (⟨0⟩ : QuillenQ (mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S)) :=
  QuillenQ.zeroComparisonIso
    (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS, max (max uR uMR + 1) (max uS uMS +
      1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S)

/-- The chosen target working zero retains its actual original descent root. -/
public def mixedOriginalQDownZeroIsoS.{uR, uS, uMR, uMS, uNR, uNS} (S : Type uS) [Ring S] :
    (QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{
      uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR
        uNS} S)).obj
      (⟨0⟩ : QuillenQ (mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S)) ≅
      (⟨0⟩ : QuillenQ (FGProjectiveCat.{max uS uMS} S)) :=
  QuillenQ.zeroComparisonIso
    (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uS, uMS, max (max uR uMR + 1) (max uS uMS +
      1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S)

/-- The actual scalar Q map between working categories. -/
public def mixedOriginalQWorkingMap.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    QuillenQ (mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R) ⥤
      QuillenQ (mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S) :=
  QuillenQ.map (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)

/-- The SAME selected working Q map has its actual original Q.map value. -/
public theorem mixedOriginalQWorkingMap_value.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    mixedOriginalQWorkingMap.{uR, uS, uMR, uMS, uNR, uNS} f =
      QuillenQ.map (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f) := by
  rfl

/-- Transport the actual canonical mapped-zero Iso through the SAME map value,
    retaining the chosen working source and target zeros. -/
public def mixedOriginalQWorkingRootIso.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (mixedOriginalQWorkingMap.{uR, uS, uMR, uMS, uNR, uNS} f).obj
        (⟨0⟩ : QuillenQ (mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R)) ≅
      (⟨0⟩ : QuillenQ (mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S)) :=
  eqToIso (congrArg (fun K : QuillenQ (mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS}
    R) ⥤
      QuillenQ (mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S) => K.obj ⟨0⟩)
    (mixedOriginalQWorkingMap_value.{uR, uS, uMR, uMS, uNR, uNS} f)) ≪≫
      QuillenQ.zeroComparisonIso (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)

/-- The complete actual root Iso is the same canonical Q zero comparison with
    only its required original map-value source transport. -/
public theorem mixedOriginalQWorkingRootIso_value.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    mixedOriginalQWorkingRootIso.{uR, uS, uMR, uMS, uNR, uNS} f =
      eqToIso (congrArg (fun K : QuillenQ (mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR,
        uNS} R) ⥤
          QuillenQ (mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S) => K.obj ⟨0⟩)
        (mixedOriginalQWorkingMap_value.{uR, uS, uMR, uMS, uNR, uNS} f)) ≪≫
          QuillenQ.zeroComparisonIso (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)
            := by
  rfl

private def originalQuillenLiftSquareRecipe.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{
      uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR
        uNS} R) ⋙
        QuillenQ.map (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f) ≅
      QuillenQ.map (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) ⋙
        QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{
          uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS)
            uNR uNS} S) := by
  let A := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R
  let B := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S
  let W := mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  exact (eqToIso (QuillenQ.map_comp A W)).symm ≪≫
    QuillenQ.mapNatIso (A ⋙ W) (F ⋙ B) (mixedOriginalProjectiveLiftSquare.{uR, uS, uMR, uMS, uNR,
      uNS} f) ≪≫
      eqToIso (QuillenQ.map_comp F B)

private def originalQuillenLiftSquareComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{
      uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR
        uNS} R) ⋙ mixedOriginalQWorkingMap.{uR, uS, uMR, uMS, uNR, uNS} f ≅
      QuillenQ.map (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) ⋙
        QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{
          uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS)
            uNR uNS} S) := by
  let A := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R
  exact eqToIso (congrArg (Functor.comp (QuillenQ.map A))
    (mixedOriginalQWorkingMap_value.{uR, uS, uMR, uMS, uNR, uNS} f)) ≪≫
      originalQuillenLiftSquareRecipe.{uR, uS, uMR, uMS, uNR, uNS} f

/-- The whole actual mixed Q lift square is induced by the original scalar square. -/
public def mixedOriginalQuillenLiftSquare.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{
      uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR
        uNS} R) ⋙ mixedOriginalQWorkingMap.{uR, uS, uMR, uMS, uNR, uNS} f ≅
      QuillenQ.map (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) ⋙
        QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{
          uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS)
            uNR uNS} S) :=
  originalQuillenLiftSquareComputed.{uR, uS, uMR, uMS, uNR, uNS} f

private theorem originalQFunctorEqualityHomApp.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {F G : C ⥤ D} (h : F = G) (X : C) :
    (eqToHom h).app X = eqToHom (congrArg (fun k : C ⥤ D => k.obj X) h) := by
  cases h
  rfl

/-- Actual functor equalities transport a natural-Iso application by their
    exact source/target object Isos, in independently sized categories. -/
public theorem mixedOriginalQuillenLiftSquare_app.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {F F' G G' : C ⥤ D} (hF : F = F') (hG : G' = G) (e : F' ≅ G') (X : C) :
    (eqToIso hF ≪≫ e ≪≫ eqToIso hG).app X =
      eqToIso (congrArg (fun K : C ⥤ D => K.obj X) hF) ≪≫ e.app X ≪≫
        eqToIso (congrArg (fun K : C ⥤ D => K.obj X) hG) := by
  cases hF
  cases hG
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_refl]

private theorem originalQFunctorEqualityMapIso.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {F G : C ⥤ D} (h : F = G) {X Y : C} (a : X ≅ Y) :
    F.mapIso a ≪≫ eqToIso (congrArg (fun K : C ⥤ D => K.obj Y) h) =
      eqToIso (congrArg (fun K : C ⥤ D => K.obj X) h) ≪≫ G.mapIso a := by
  cases h
  simp only [eqToIso_refl, Iso.trans_refl, Iso.refl_trans]

/-- The same scalar Q-square recipe is preceded only by its actual selected
    WorkingMap=value source transport. -/
public theorem mixedOriginalQuillenLiftSquare_value.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    mixedOriginalQuillenLiftSquare.{uR, uS, uMR, uMS, uNR, uNS} f =
      eqToIso (congrArg (Functor.comp (QuillenQ.map
        (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS uMS
          + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R)))
        (mixedOriginalQWorkingMap_value.{uR, uS, uMR, uMS, uNR, uNS} f)) ≪≫
          ((eqToIso (QuillenQ.map_comp
            (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS
              uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R)
            (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f))).symm ≪≫
          QuillenQ.mapNatIso
            (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS
              uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R ⋙
              mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)
            (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f ⋙
              FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS, max (max uR uMR + 1) (max
                uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S)
            (mixedOriginalProjectiveLiftSquare.{uR, uS, uMR, uMS, uNR, uNS} f) ≪≫
          eqToIso (QuillenQ.map_comp (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
            (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS, max (max uR uMR + 1) (max uS
              uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S))) := by
  rfl

private theorem originalQuillenLiftSquareRecipeApp.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (X : QuillenQ (FGProjectiveCat.{max uR uMR} R)) :
    (originalQuillenLiftSquareRecipe.{uR, uS, uMR, uMS, uNR, uNS} f).app X =
      (QuillenQ.mapNatIso
        (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS uMS
          + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R ⋙
          mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)
        (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f ⋙
          FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS, max (max uR uMR + 1) (max uS
            uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S)
        (mixedOriginalProjectiveLiftSquare.{uR, uS, uMR, uMS, uNR, uNS} f)).app X := by
  let A := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R
  let B := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S
  let W := mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let e := mixedOriginalProjectiveLiftSquare.{uR, uS, uMR, uMS, uNR, uNS} f
  apply Iso.ext
  change (eqToHom (QuillenQ.map_comp A W).symm).app X ≫
      (QuillenQ.mapNatIso (A ⋙ W) (F ⋙ B) e).hom.app X ≫
        (eqToHom (QuillenQ.map_comp F B)).app X =
    (QuillenQ.mapNatIso (A ⋙ W) (F ⋙ B) e).hom.app X
  let hSource := congrArg (fun K => K.obj X) (QuillenQ.map_comp A W).symm
  let hTarget := congrArg (fun K => K.obj X) (QuillenQ.map_comp F B)
  let m := (QuillenQ.mapNatIso (A ⋙ W) (F ⋙ B) e).hom.app X
  have hLeft : (eqToHom (QuillenQ.map_comp A W).symm).app X = eqToHom hSource :=
    originalQFunctorEqualityHomApp (QuillenQ.map_comp A W).symm X
  have hRight : (eqToHom (QuillenQ.map_comp F B)).app X = eqToHom hTarget :=
    originalQFunctorEqualityHomApp (QuillenQ.map_comp F B) X
  have hValue : (eqToHom (QuillenQ.map_comp A W).symm).app X ≫ m ≫
      (eqToHom (QuillenQ.map_comp F B)).app X = eqToHom hSource ≫ m ≫ eqToHom hTarget :=
    congrArg₂ (fun a b => a ≫ m ≫ b) hLeft hRight
  have hCast : HEq (eqToHom hSource ≫ m ≫ eqToHom hTarget) m :=
    (CategoryTheory.eqToHom_comp_heq (m ≫ eqToHom hTarget) hSource).trans
      (CategoryTheory.comp_eqToHom_heq m hTarget)
  exact eq_of_heq ((heq_of_eq hValue).trans hCast)

private theorem originalQuillenLiftSquareActualApp.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (X : QuillenQ (FGProjectiveCat.{max uR uMR} R)) :
    (mixedOriginalQuillenLiftSquare.{uR, uS, uMR, uMS, uNR, uNS} f).app X =
      eqToIso (congrArg
        (fun K : QuillenQ (mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R) ⥤
          QuillenQ (mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S) => K.obj
            ((QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{
              uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS
                uMS) uNR uNS} R)).obj X))
        (mixedOriginalQWorkingMap_value.{uR, uS, uMR, uMS, uNR, uNS} f)) ≪≫
          (originalQuillenLiftSquareRecipe.{uR, uS, uMR, uMS, uNR, uNS} f).app X := by
  let A := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R
  let h := congrArg (Functor.comp (QuillenQ.map A))
    (mixedOriginalQWorkingMap_value.{uR, uS, uMR, uMS, uNR, uNS} f)
  have hSquare := congrArg (fun e => e.app X)
    (mixedOriginalQuillenLiftSquare_value.{uR, uS, uMR, uMS, uNR, uNS} f)
  have hApp := mixedOriginalQuillenLiftSquare_app h rfl
    (originalQuillenLiftSquareRecipe.{uR, uS, uMR, uMS, uNR, uNS} f) X
  have hValue : (eqToIso h ≪≫ originalQuillenLiftSquareRecipe.{uR, uS, uMR, uMS, uNR, uNS} f).app
    X =
      eqToIso (congrArg
        (fun K : QuillenQ (mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R) ⥤
          QuillenQ (mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S) => K.obj
            ((QuillenQ.map A).obj X))
        (mixedOriginalQWorkingMap_value.{uR, uS, uMR, uMS, uNR, uNS} f)) ≪≫
          (originalQuillenLiftSquareRecipe.{uR, uS, uMR, uMS, uNR, uNS} f).app X := by
    simpa only [eqToIso_refl, Iso.trans_refl] using hApp
  exact hSquare.trans hValue

private theorem originalQuillenLiftSquareRecipeRoot.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (originalQuillenLiftSquareRecipe.{uR, uS, uMR, uMS, uNR, uNS} f).app
        (⟨0⟩ : QuillenQ (FGProjectiveCat.{max uR uMR} R)) ≪≫
      ((QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{
        uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR
          uNS} S)).mapIso
        (QuillenQ.zeroComparisonIso (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)) ≪≫
          mixedOriginalQUpZeroIsoS.{uR, uS, uMR, uMS, uNR, uNS} S) =
      (QuillenQ.map (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)).mapIso
        (mixedOriginalQUpZeroIsoR.{uR, uS, uMR, uMS, uNR, uNS} R) ≪≫
          QuillenQ.zeroComparisonIso (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)
            := by
  let A := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R
  let B := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S
  let W := mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let e := mixedOriginalProjectiveLiftSquare.{uR, uS, uMR, uMS, uNR, uNS} f
  let X : QuillenQ (FGProjectiveCat.{max uR uMR} R) := ⟨0⟩
  have hNat := QuillenQ.zeroComparisonIso_naturality (A ⋙ W) (F ⋙ B) e
  have hRight := QuillenQ.zeroComparisonIso_comp F B
  have hLeft := QuillenQ.zeroComparisonIso_comp A W
  have hRoots : (QuillenQ.mapNatIso (A ⋙ W) (F ⋙ B) e).app X ≪≫
      ((QuillenQ.map B).mapIso (QuillenQ.zeroComparisonIso F) ≪≫
        QuillenQ.zeroComparisonIso B) =
      (QuillenQ.map W).mapIso (QuillenQ.zeroComparisonIso A) ≪≫
        QuillenQ.zeroComparisonIso W :=
    (congrArg (fun r => (QuillenQ.mapNatIso (A ⋙ W) (F ⋙ B) e).app X ≪≫ r)
      hRight.symm).trans (hNat.trans hLeft)
  exact (congrArg (fun a => a ≪≫
    ((QuillenQ.map B).mapIso (QuillenQ.zeroComparisonIso F) ≪≫ QuillenQ.zeroComparisonIso B))
    (originalQuillenLiftSquareRecipeApp.{uR, uS, uMR, uMS, uNR, uNS} f X)).trans hRoots

/-- The SAME actual Q lift square follows both original canonical roots,
    using only the necessary selected-map value source casts. -/
public theorem mixedOriginalQuillenLiftSquare_zero.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (mixedOriginalQuillenLiftSquare.{uR, uS, uMR, uMS, uNR, uNS} f).app
        (⟨0⟩ : QuillenQ (FGProjectiveCat.{max uR uMR} R)) ≪≫
      ((QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{
        uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR
          uNS} S)).mapIso
        (QuillenQ.zeroComparisonIso (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)) ≪≫
          mixedOriginalQUpZeroIsoS.{uR, uS, uMR, uMS, uNR, uNS} S) =
      (mixedOriginalQWorkingMap.{uR, uS, uMR, uMS, uNR, uNS} f).mapIso
        (mixedOriginalQUpZeroIsoR.{uR, uS, uMR, uMS, uNR, uNS} R) ≪≫
        mixedOriginalQWorkingRootIso.{uR, uS, uMR, uMS, uNR, uNS} f := by
  let A := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R
  let B := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS, max (max uR uMR + 1) (max uS
    uMS + 1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S
  let W := mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f
  let M := mixedOriginalQWorkingMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let X : QuillenQ (FGProjectiveCat.{max uR uMR} R) := ⟨0⟩
  let Z : QuillenQ (mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R) := ⟨0⟩
  let h := mixedOriginalQWorkingMap_value.{uR, uS, uMR, uMS, uNR, uNS} f
  let p := mixedOriginalQUpZeroIsoR.{uR, uS, uMR, uMS, uNR, uNS} R
  let q := QuillenQ.zeroComparisonIso W
  let r := (QuillenQ.map B).mapIso (QuillenQ.zeroComparisonIso F) ≪≫
    mixedOriginalQUpZeroIsoS.{uR, uS, uMR, uMS, uNR, uNS} S
  let s := eqToIso (congrArg (fun K => K.obj ((QuillenQ.map A).obj X)) h)
  let z := eqToIso (congrArg (fun K => K.obj Z) h)
  have hApp := originalQuillenLiftSquareActualApp.{uR, uS, uMR, uMS, uNR, uNS} f X
  have hBase := originalQuillenLiftSquareRecipeRoot.{uR, uS, uMR, uMS, uNR, uNS} f
  have hMap : M.mapIso p ≪≫ z = s ≪≫ (QuillenQ.map W).mapIso p :=
    originalQFunctorEqualityMapIso h p
  have hRoot : mixedOriginalQWorkingRootIso.{uR, uS, uMR, uMS, uNR, uNS} f = z ≪≫ q :=
    mixedOriginalQWorkingRootIso_value.{uR, uS, uMR, uMS, uNR, uNS} f
  calc
    (mixedOriginalQuillenLiftSquare.{uR, uS, uMR, uMS, uNR, uNS} f).app X ≪≫ r =
        (s ≪≫ (originalQuillenLiftSquareRecipe.{uR, uS, uMR, uMS, uNR, uNS} f).app X) ≪≫ r :=
      congrArg (fun a => a ≪≫ r) hApp
    _ = s ≪≫ ((originalQuillenLiftSquareRecipe.{uR, uS, uMR, uMS, uNR, uNS} f).app X ≪≫ r) :=
      Iso.trans_assoc _ _ _
    _ = s ≪≫ ((QuillenQ.map W).mapIso p ≪≫ q) := congrArg (Iso.trans s) hBase
    _ = (s ≪≫ (QuillenQ.map W).mapIso p) ≪≫ q := (Iso.trans_assoc _ _ _).symm
    _ = (M.mapIso p ≪≫ z) ≪≫ q := congrArg (fun a => a ≪≫ q) hMap.symm
    _ = M.mapIso p ≪≫ (z ≪≫ q) := Iso.trans_assoc _ _ _
    _ = M.mapIso p ≪≫ mixedOriginalQWorkingRootIso.{uR, uS, uMR, uMS, uNR, uNS} f :=
      congrArg (Iso.trans (M.mapIso p)) hRoot.symm

end AlgebraicKTheory.StableGL

end
