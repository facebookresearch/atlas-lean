/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TorusBorelEulerModels

/-!
# Character-normalized native Borel polynomial actions

Coordinate classes are actual zero-section Euler classes of the
character line at the scheme point, relative to the coefficient system's
one orientation datum, transported by the native finite Borel and
point-projection comparisons. They are the usual generators of equivariant
cohomology of a point when that datum is the complex orientation;
otherwise each is a unit multiple of it. Each polynomial generator acts by
the corresponding actual Borel cup on every cohomology class. The
endomorphism algebra is not assumed commutative.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.TorusBorelCoefficientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open IntegralChowChernModels AlgebraicWeightBundleModels AlgebraicSplitTorusModels
open TorusPolynomialDegreeModels TorusDifferentialGeometryModels SymplecticTorusSourceModels
open LinearizedLineBundles ComplexAnalytification CoefficientBettiModels
open FiniteTorusBorelApproximationModels TorusBorelEulerModels
open CoherentCurveLinearSeries
open MathlibExt.Topology.ContinuousBorel
open scoped DirectSum

instance pointGroupAction (T : Over base) [GrpObj T] : ModObj T pointData.scheme :=
  trivialGroupAction T pointData.scheme

variable {T : Over base} [GrpObj T] (M : TorusModel T)

/-- This is the existing Borel cohomology of the original analytified action. -/
abbrev H (X : Over base) [ModObj T X] (A : AnalyticTorusAction M X) :=
  letI := A.action
  letI := A.continuous
  BorelCohomologyModels.GradedH (Fin M.rank → ℂˣ) (space X)

/-- The homogeneous inclusion is the native cohomology direct-sum map. -/
def homogeneous (X : Over base) [ModObj T X] (A : AnalyticTorusAction M X) (n : ℤ) :
    letI := A.action
    letI := A.continuous
    BorelCohomologyModels.H (Fin M.rank → ℂˣ) (space X) n →ₗ[ℂ] H M X A := by
  letI := A.action
  letI := A.continuous
  exact DirectSum.lof ℂ ℤ (BorelCohomologyModels.H (Fin M.rank → ℂˣ) (space X)) n

/-- The unit is the actual coefficient-unit morphism in native degree zero. -/
def gradedUnit (X : Over base) [ModObj T X] (A : AnalyticTorusAction M X) : H M X A := by
  letI := A.action
  letI := A.continuous
  exact homogeneous M X A 0 (unitClass ℂ (borel (Fin M.rank → ℂˣ) (space X)))

/-- The generator line has its original Laurent character and inverse fibre transport; its
Euler geometry is oriented by the given datum. -/
structure CoordinateLineSource (O : OrientationData) (j : Fin M.rank) where
  character : Character T
  coordinate : character.map.left.appTop (gmUnit : Γ(Gm.left, ⊤)) =
    (coordinateUnit M j : Γ(T.left, ⊤))
  linearization : Linearization T pointData.scheme (structureModule pointData.scheme.left)
  normalized : linearization.comparison.hom =
    scalarEnd (T ⊗ pointData.scheme).left
      ((Scheme.Modules.pullback (snd T pointData.scheme).left).obj
        (structureModule pointData.scheme.left))
      (inverseCharacterFunction character pointData.scheme)
  point : AnalyticTorusAction M pointData.scheme
  pointComparison : letI := point.action
    letI := point.continuous
    ∀ n : ℤ, Function.Bijective
      (cohomologyPullback ℂ
        (BorelCohomologyModels.pointProjection (Fin M.rank → ℂˣ) (space pointData.scheme)) n)
  [stageAction : ModObj T (MixedTotal M pointData 1)]
  stageAnalytic : AnalyticTorusAction M (MixedTotal M pointData 1)
  stage : MixedStage M pointData point 1 stageAnalytic
  geometry : EquivariantEulerGeometry M pointData point 1 stageAnalytic stage linearization O 1

/-- A coefficient is that prescribed native character Euler, under the actual point comparison. -/
def CoordinateLineSource.coefficient {O : OrientationData} {j : Fin M.rank}
    (S : CoordinateLineSource M O j) :
    BorelCohomologyModels.CoefficientH (Fin M.rank → ℂˣ) 2 := by
  letI := S.point.action
  letI := S.point.continuous
  letI := S.stageAction
  exact (LinearEquiv.ofBijective
    (cohomologyPullback ℂ
      (BorelCohomologyModels.pointProjection (Fin M.rank → ℂˣ) (space pointData.scheme)) 2)
    (S.pointComparison 2)).symm
      (EquivariantEulerGeometry.euler M pointData S.point 1 S.stageAnalytic S.stage
        S.linearization S.geometry)

/-- Every generator comes from the actual corresponding coordinate-character line, all oriented
by one shared datum. -/
structure CoefficientCoordinates where
  /-- The one orientation datum used for every Euler class of this coefficient system. -/
  orientation : OrientationData
  line : ∀ j : Fin M.rank, CoordinateLineSource M orientation j

variable (P : CoefficientCoordinates M) (X : Over base) [ModObj T X]
  (A : AnalyticTorusAction M X)

/-- The polynomial action is fixed on every generator and every native cohomology class. -/
structure PolynomialAction where
  action : CharacterPolynomials M.rank →ₐ[ℂ] Module.End ℂ (H M X A)
  generator : ∀ j : Fin M.rank,
    action (MvPolynomial.X j) =
      letI := A.action
      letI := A.continuous
      BorelCohomologyModels.coefficientAction (Fin M.rank → ℂˣ) (space X) 2
        (CoordinateLineSource.coefficient M (P.line j))

end MathlibExt.AlgebraicGeometry.TorusBorelCoefficientModels
