/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoefficientProperDualityModels
public import MathlibExt.AlgebraicGeometry.GlobalZeroSectionRecipe
public import MathlibExt.AlgebraicGeometry.FiniteTorusBorelApproximationModels

/-!
# Actual zero-section Euler classes in finite Borel approximations

The ordinary Euler class is the actual proper zero-section push of
the smooth fundamental class, followed by the inverse of the actual
bundle-projection cohomology map. The equivariant class uses the
native finite-approximation comparison. The associated module is
identified with the original pulled equivariant module; its descent
equation fixes the torus action, including character twists.
No independent Euler class or cohomological push operator is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.TorusBorelEulerModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open ConstructibleComplexes IntegralChowChernModels ComplexAnalytification
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels LinearizedLineBundles
open SymplecticTorusSourceModels FiniteTorusBorelApproximationModels
open CoefficientBettiModels CoefficientCompactSupportModels CoefficientProperDualityModels
attribute [local instance] HasDerivedCategory.standard

/-- Only the actual integer cohomological degree is changed. -/
def cohomologyCast {Z : TopCat.{0}} {i j : ℤ} (h : i=j) :
    CoefficientBettiModels.Cohomology ℂ Z i →ₗ[ℂ] CoefficientBettiModels.Cohomology ℂ Z j := by
  cases h
  exact LinearMap.id

/-- Native zero-section geometry and its actual compact-support duality. -/
structure ZeroEulerGeometry (X : SchemeData) (E : X.scheme.left.Modules) (r : ℕ) where
  bundle : GlobalZeroSectionRecipe.VectorBundleModel X.scheme E r
  dimension : ℕ
  [baseSmooth : SmoothOfRelativeDimension dimension X.scheme.hom]
  [totalSmooth : SmoothOfRelativeDimension (dimension+r) bundle.total.hom]
  [closed : IsClosedImmersion (GlobalZeroSectionRecipe.zeroSection bundle).left]
  baseDuality : DualizingComplex ℂ (space X.scheme)
  totalDuality : DualizingComplex ℂ (space bundle.total)
  basePurity : baseDuality.obj ≅ (coefficientUnit ℂ (space X.scheme))⟦(2*dimension : ℤ)⟧
  totalPurity : totalDuality.obj ≅
    (coefficientUnit ℂ (space bundle.total))⟦(2*(dimension+r) : ℤ)⟧
  zeroPullback : ProperPullback ℂ (spaceMap (GlobalZeroSectionRecipe.zeroSection bundle))
  homotopy : ∀ n : ℤ, Function.Bijective
    (cohomologyPullback ℂ (spaceMap bundle.projection) n)

attribute [instance] ZeroEulerGeometry.baseSmooth ZeroEulerGeometry.totalSmooth
  ZeroEulerGeometry.closed

/-- The zero-section class is computed from native proper push and the same smooth purity. -/
def ZeroEulerGeometry.zeroClass {X : SchemeData} {E : X.scheme.left.Modules} {r : ℕ}
    (G : ZeroEulerGeometry X E r) : CoefficientBettiModels.Cohomology ℂ (space G.bundle.total) (2*r)
      :=
  cohomologyCast (show (2*(G.dimension+r) : ℤ)-(2*G.dimension : ℤ) = (2*r : ℤ) by omega)
    ((purityHomologyEquiv ℂ (space G.bundle.total) G.totalDuality (G.dimension+r)
      G.totalPurity (2*G.dimension)).toLinearMap
      (borelMoorePushforward ℂ G.zeroPullback G.baseDuality G.totalDuality (2*G.dimension)
        (fundamentalClass ℂ (space X.scheme) G.baseDuality G.dimension G.basePurity)))

/-- The Euler class is the inverse actual bundle pullback of that zero-section class. -/
def ZeroEulerGeometry.euler {X : SchemeData} {E : X.scheme.left.Modules} {r : ℕ}
    (G : ZeroEulerGeometry X E r) : CoefficientBettiModels.Cohomology ℂ (space X.scheme) (2*r) :=
  (LinearEquiv.ofBijective (cohomologyPullback ℂ (spaceMap G.bundle.projection) (2*r))
    (G.homotopy (2*r))).symm G.zeroClass

/-- The pulled bundle comparison is the actual action/projection square of its original map. -/
def pulledLinearComparison {T Y Z : Over base} [GrpObj T] [ModObj T Y] [ModObj T Z]
    (f : Y ⟶ Z) (hf : γ[T,Y] ≫ f = (T ◁ f) ≫ γ[T,Z])
    {E : Z.left.Modules} (L : Linearization T Z E) :
    (Scheme.Modules.pullback γ[T,Y].left).obj ((Scheme.Modules.pullback f.left).obj E) ⟶
      (Scheme.Modules.pullback (snd T Y).left).obj ((Scheme.Modules.pullback f.left).obj E) :=
  (Scheme.Modules.pullbackComp γ[T,Y].left f.left).hom.app E ≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hf)).hom.app E ≫
    reindexHom (T ◁ f).left L.comparison.hom ≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (whiskerLeft_snd T f))).hom.app E ≫
    (Scheme.Modules.pullbackComp (snd T Y).left f.left).inv.app E

/-- A module from the actual invariant quotient has its literal trivial relative transport. -/
def invariantPullbackComparison {T Y Z : Over base} [GrpObj T] [ModObj T Y]
    (f : Y ⟶ Z) (hf : γ[T,Y] ≫ f = snd T Y ≫ f) (E : Z.left.Modules) :
    (Scheme.Modules.pullback γ[T,Y].left).obj ((Scheme.Modules.pullback f.left).obj E) ⟶
      (Scheme.Modules.pullback (snd T Y).left).obj ((Scheme.Modules.pullback f.left).obj E) :=
  (Scheme.Modules.pullbackComp γ[T,Y].left f.left).hom.app E ≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hf)).hom.app E ≫
    (Scheme.Modules.pullbackComp (snd T Y).left f.left).inv.app E

variable {T : Over base} [GrpObj T] (M : TorusModel T) (X : SchemeData) [ModObj T X.scheme]
  (AX : AnalyticTorusAction M X.scheme) (m : ℕ)
  [ModObj T (MixedTotal M X m)] (A : AnalyticTorusAction M (MixedTotal M X m))
  (P : MixedStage M X AX m A) {E : X.scheme.left.Modules} (L : Linearization T X.scheme E)

/-- Descent retains the original module and its complete actual torus transport. -/
structure AssociatedModule where
  module : P.quotient.quotient.scheme.left.Modules
  comparison : (Scheme.Modules.pullback P.quotient.projection.left).obj module ≅
    (Scheme.Modules.pullback (snd (freeApproximation M.rank m) X.scheme).left).obj E
  equivariant :
    (Scheme.Modules.pullback γ[T,MixedTotal M X m].left).map comparison.hom ≫
      pulledLinearComparison (snd (freeApproximation M.rank m) X.scheme) P.projection L =
    invariantPullbackComparison P.quotient.projection P.quotient.invariant module ≫
      (Scheme.Modules.pullback (snd T (MixedTotal M X m)).left).map comparison.hom

/-- The finite-stage Euler geometry is for that exact descended original module. -/
structure EquivariantEulerGeometry (r : ℕ) where
  associated : AssociatedModule M X AX m A P L
  zero : ZeroEulerGeometry P.quotient.quotient associated.module r
  stableRange : (2*r : ℤ) < 2*m+1

/-- The class is transported by the actual finite Borel comparison, with no Borel properness
  assumption. -/
def EquivariantEulerGeometry.euler {r : ℕ}
    (G : EquivariantEulerGeometry M X AX m A P L r) :
    letI := AX.action
    letI := AX.continuous
    BorelCohomologyModels.H (Fin M.rank → ℂˣ) (space X.scheme) (2*r) := by
  letI := AX.action
  letI := AX.continuous
  exact (MixedStage.comparison M X AX m A P (2*r) G.stableRange).symm G.zero.euler

end MathlibExt.AlgebraicGeometry.TorusBorelEulerModels
