/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PositiveCurveDeterminants
public import MathlibExt.AlgebraicGeometry.NativeLineDuals
public import MathlibExt.AlgebraicGeometry.ModuleDerivedSquares

/-!
# Actual curve cohomology determinant operations

Rpi_* is the native module-derived pushforward of the actual degree-zero
sheaf complex. Its base-change map is the native derived-adjunction mate,
followed by the native pullback counit and single-complex comparison.
Determinants use the entire [0,1] inverse-shift affine normalization.

The construction dictionary below does not assume any Poincare, Picard,
autoduality or Fourier--Mukai theorem. It assembles the separately requested
native determinant/dual objects and their fixed comparison maps.
Sources: Knudsen--Mumford Sections 1--2; MRV arXiv:1207.7233v5,
Section 5; pinned Mathlib/Stacks notices in the imported modules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CurveCohomologyDeterminantModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open FourierMukai PositiveCurveDeterminants NativeLineDuals ModuleDerivedSquares
open SchemeDeterminantPresentations AffineDerivedCoefficientModules
open CoherentCurveLinearSeries

attribute [local instance] HasDerivedCategory.standard

variable [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]

structure DeterminantSystem (S : AffineSources) where
  value : ∀ (X : Scheme.{0}) (K : FourierMukai.D X),
    IsPerfectTwoTermOn (K⟦(1 : ℤ)⟧) → CurveDeterminantData S K
  comparison : ∀ (X : Scheme.{0}) {K L : FourierMukai.D X}
    (pK : IsPerfectTwoTermOn (K⟦(1 : ℤ)⟧)) (pL : IsPerfectTwoTermOn (L⟦(1 : ℤ)⟧))
    (e : K⟦(1 : ℤ)⟧ ≅ L⟦(1 : ℤ)⟧), LineComparison S e (value X K pK) (value X L pL)
  pullback : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) {K : FourierMukai.D X} {L : FourierMukai.D Y}
    (pK : IsPerfectTwoTermOn (K⟦(1 : ℤ)⟧)) (pL : IsPerfectTwoTermOn (L⟦(1 : ℤ)⟧))
    (e : (derivedPullback f).obj (K⟦(1 : ℤ)⟧) ≅ L⟦(1 : ℤ)⟧),
      PullbackLineComparison S f e (value X K pK) (value Y L pL)
  duality : ∀ (X : Scheme.{0}) (L : X.Modules), IsLineBundle L → LineDuality X L

variable [HasDerivedPushforwards.{0}]

def singleModule {X : Scheme.{0}} (F : X.Modules) : FourierMukai.D X :=
  DerivedCategory.Q.obj ((CochainComplex.singleFunctor X.Modules 0).obj F)

def cohomologyObject {X T : Scheme.{0}} (p : X ⟶ T) (F : X.Modules) : FourierMukai.D T :=
  (derivedPushforward p).obj (singleModule F)

def determinantOfCohomology {S : AffineSources} (A : DeterminantSystem S)
    {X T : Scheme.{0}} (p : X ⟶ T) (F : X.Modules)
    (perfect : IsPerfectTwoTermOn ((cohomologyObject p F)⟦(1 : ℤ)⟧)) :
    CurveDeterminantData S (cohomologyObject p F) := A.value T (cohomologyObject p F) perfect

/-- Actual proper-cohomology base change, with no independently supplied map. -/
def nativeCohomologyBaseChange {X' X T' T : Scheme.{0}}
    (a : X' ⟶ X) (p' : X' ⟶ T') (p : X ⟶ T) (g : T' ⟶ T)
    (comm : a ≫ p = p' ≫ g) (F : X.Modules)
    (P : PullPushAdjunction p) (P' : PullPushAdjunction p')
    (C : PullbackPasting p' g) (B : PullbackPasting a p) :
    (derivedPullback g).obj (cohomologyObject p F) ⟶
      cohomologyObject p' ((Scheme.Modules.pullback a).obj F) :=
  baseChangeMap a p' p g comm P P' C B (singleModule F) ≫
    (derivedPushforward p').map
      ((derivedPullbackCounit a).app ((CochainComplex.singleFunctor X.Modules 0).obj F) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            (Scheme.Modules.pullback a) (.up ℤ) 0).hom.app F))

end MathlibExt.AlgebraicGeometry.CurveCohomologyDeterminantModels
