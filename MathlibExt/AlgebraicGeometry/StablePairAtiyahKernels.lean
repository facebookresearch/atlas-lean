/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StablePairDiagonalIdeals
public import MathlibExt.AlgebraicGeometry.ModuleDerivedSquares

/-!
# The actual Huybrechts–Thomas universal truncated Atiyah kernel

The source is the concrete diagonal resolution in degrees -2,-1,0.
The target has the same actual kernel and the actual ambient diagonal
conormal quotient. Its map is identity/projection/zero, exactly the
source diagram (2.6).

The resulting cotangent model is pulled to the diagonal. Its shifted
pushforward comparison is the native pullback/pushforward unit and
right-derived pushforward unit, with the actual shift cancellation.
Thus the universal class is a computed composite of genuine kernel
maps, rather than a named element of Ext.

Reference: Huybrechts–Thomas, arXiv:0805.3527v2, Lemma 2.2,
Definitions 2.3 and 2.6, equations (2.3)–(2.6).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairAtiyahKernels

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries StablePairDiagonalIdeals
open FourierMukai ModuleDerivedSquares
open scoped ZeroObject
attribute [local instance] HasDerivedCategory.standard

variable {Y Z : Over (Spec (.of ℂ))} (i : Y ⟶ Z)
  (S : IdealSquare (diagonal Z))

/-- The literal three-term resolution of the small diagonal. -/
def resolution : CochainComplex (pullback Y.hom Y.hom).Modules ℤ :=
  StablePairJetComplexes.complex (diagonalKernel i) (restrictedIdeal i)
    (structureModule (pullback Y.hom Y.hom))
    (kernel.ι (restrictedIdealMap i)) (restrictedIdealMap i) (kernel.condition _)

/-- The identity/projection target of the universal truncated class. -/
def target : CochainComplex (pullback Y.hom Y.hom).Modules ℤ :=
  StablePairJetComplexes.complex (diagonalKernel i) (restrictedQuotient i S) 0
    (kernel.ι (restrictedIdealMap i) ≫ quotientProjection i S) 0 (by simp)

/-- The diagonal-pulled target, shifted into cotangent degrees -1 and 0. -/
def cotangent : CochainComplex Y.left.Modules ℤ :=
  (((Scheme.Modules.pullback (diagonal Y)).mapHomologicalComplex (.up ℤ)).obj
    (target i S))⟦(-1 : ℤ)⟧

/-- The source augmentation is fixed to the actual small-diagonal structure map. -/
structure ResolutionAugmentation where
  map : resolution i ⟶ (CochainComplex.singleFunctor (pullback Y.hom Y.hom).Modules 0).obj
    ((Scheme.Modules.pushforward (diagonal Y)).obj (structureModule Y.left))
  normalized : map.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      ((Scheme.Modules.pushforward (diagonal Y)).obj (structureModule Y.left))).hom =
    RationalResolution.structureUnit (diagonal Y)
  [quasiIso : QuasiIso map]

attribute [instance] ResolutionAugmentation.quasiIso

/-- The universal map has its three source components fixed. -/
structure KernelProjection where
  map : resolution i ⟶ target i S
  negative_two : map.f (-2) = 𝟙 (diagonalKernel i)
  negative_one : map.f (-1) = quotientProjection i S
  zero : map.f 0 = 0

variable [HasDerivedPushforwards.{0}]

/-- The particular shift cancellation used by the source construction. -/
def cancelShift :
    (cotangent i S)⟦(1 : ℤ)⟧ ≅
      ((Scheme.Modules.pullback (diagonal Y)).mapHomologicalComplex (.up ℤ)).obj (target i S) := by
  let K := ((Scheme.Modules.pullback (diagonal Y)).mapHomologicalComplex (.up ℤ)).obj
    (target i S)
  change (K⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ K
  change ((CochainComplex.shiftFunctor Y.left.Modules 1).obj
    ((CochainComplex.shiftFunctor Y.left.Modules (-1)).obj K)) ≅ K
  exact ((CochainComplex.shiftFunctorAdd' Y.left.Modules (-1) 1 0 (by omega)).app K).symm ≪≫
    (CochainComplex.shiftFunctorZero' Y.left.Modules 0 rfl).app K

/-- The actual comparison to the shifted diagonal direct image. -/
def targetPushMap :
    DerivedCategory.Q.obj (target i S) ⟶
      (derivedPushforward (diagonal Y)).obj (DerivedCategory.Q.obj ((cotangent i S)⟦(1 : ℤ)⟧)) :=
  DerivedCategory.Q.map (cochainUnit (diagonal Y) (target i S)) ≫
    (derivedPushforwardUnit (diagonal Y)).app
      (((Scheme.Modules.pullback (diagonal Y)).mapHomologicalComplex (.up ℤ)).obj (target i S)) ≫
      (derivedPushforward (diagonal Y)).map (DerivedCategory.Q.map (cancelShift i S).inv)

/-- The actual universal truncated Atiyah class, assembled from the source diagram. -/
def universalClass (A : ResolutionAugmentation i) (P : KernelProjection i S)
    (_h : IsIso (targetPushMap i S)) :
    DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (pullback Y.hom Y.hom).Modules 0).obj
        ((Scheme.Modules.pushforward (diagonal Y)).obj (structureModule Y.left))) ⟶
      (derivedPushforward (diagonal Y)).obj
        (DerivedCategory.Q.obj ((cotangent i S)⟦(1 : ℤ)⟧)) :=
  inv (DerivedCategory.Q.map A.map) ≫ DerivedCategory.Q.map P.map ≫ targetPushMap i S

end MathlibExt.AlgebraicGeometry.StablePairAtiyahKernels
