/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeRationalCurveRealizations
public import MathlibExt.AlgebraicGeometry.NativeIndDifferentialContexts
public import MathlibExt.AlgebraicGeometry.RightCoordinateDifferentials

/-!
# Actual rational-curve modules in the native full differential ring

The curve is the original punctured complex line with its original
holomorphic inclusion. Module sections are the actual holomorphic vector
functions, with original restriction/scalar action. The actual z
coordinate and source derivative-minus-A action fix the full native D
module through local scalar/derivative generation. This ties the curve
normalizations to the same ordinary D-module carrier used by H01.

Source: the already sourced RegularSingularConnections scope;
DK1311.2374v2 Section2.5/Definition9.1.1; Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeRationalCurveModuleModels

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open RegularSingularConnections NativeIndDifferentialContexts DifferentialOperatorSheaves
open DifferentialOperatorScalars RightCoordinateDifferentials
open scoped Manifold ContDiff
attribute [local instance] Classical.propDecidable

variable (S : Finset ℂ)

/-- A complex manifold structure on the punctured line that is the standard one: the inclusion
into `ℂ` is holomorphic for it. An injective holomorphic map of Riemann surfaces is biholomorphic onto
its image, so this pins the complex structure; it excludes, for instance, the conjugate atlas, for
which the inclusion is antiholomorphic. -/
class CurveComplexSource where
  [charts : ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates 1) (puncturedLine S)]
  [manifold : IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates 1) ∞ (puncturedLine S)]
  inclusionHolomorphic : ContMDiff (M := puncturedLine S) (M' := ℂ)
    𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates 1) 𝓘(ℂ, ℂ) ∞
    (Subtype.val : puncturedLine S → ℂ)

attribute [instance_reducible, instance] CurveComplexSource.charts
attribute [instance] CurveComplexSource.manifold

variable [CurveComplexSource S]
  [HasSheafify (Opens.grothendieckTopology (puncturedLine S)) RingCat.{0}]

abbrev curveCoefficients := analyticCoefficients 1 (puncturedLine S)

/-- The coordinate `z` of the punctured line and its derivation `d/dz`, for the standard complex
structure fixed by `CurveComplexSource`. -/
structure CurveCoordinateSource where
  coordinate : CoordinateDerivation ℂ (puncturedLine S) (curveCoefficients S)
  value : ∀ (U : Opens (puncturedLine S)) (x : U), (coordinate.function U).val x = x.val.val
  derivativeValues : ∀ (U : Opens (puncturedLine S))
      (a : (curveCoefficients S).obj (op U)) (x : U),
    (coordinate.derivative U a).val x =
      derivWithin (fun z => if h : z ∈ ambientOpen S U then a.val ⟨h.choose, h.choose_spec.1⟩ else 0)
        (ambientOpen S U) x.val.val
  generation : ∀ (U : Opens (puncturedLine S))
      (P : finiteOperatorRing ℂ (puncturedLine S) (curveCoefficients S) U),
    P ∈ Subring.closure (Set.range (scalarFinite ℂ (puncturedLine S) (curveCoefficients S) U) ∪
      {partialFinite ℂ (puncturedLine S) (curveCoefficients S) coordinate U})

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) RationalFunctions) (hA : PolesWithin S A)
  (C : CurveCoordinateSource S)

/-- The actual native left D-module connection, fixed on every original vector section and operator generator. -/
structure RationalConnectionModuleSource where
  object : DModule ℂ (puncturedLine S) (curveCoefficients S)
  sections : ∀ U : Opens (puncturedLine S), object.val.obj (op U) ≃+ holomorphicSections S r U
  restriction : ∀ (U V : Opens (puncturedLine S)) (h : V ≤ U) (s : object.val.obj (op U))
      (x : V),
    (sections V ((object.val.map (homOfLE h).op).hom s)).val x.val.val =
      (sections U s).val x.val.val
  scalar : ∀ (U : Opens (puncturedLine S)) (a : (curveCoefficients S).obj (op U))
      (s : object.val.obj (op U)) (x : U) (i : Fin r),
    (sections U (((toSheafify (Opens.grothendieckTopology (puncturedLine S))
      (operatorPresheaf ℂ (puncturedLine S) (curveCoefficients S))).app (op U)).hom
        (scalarFinite ℂ (puncturedLine S) (curveCoefficients S) U a) • s)).val x.val.val i =
          a.val x * (sections U s).val x.val.val i
  derivative : ∀ (U : Opens (puncturedLine S)) (s : object.val.obj (op U)) (x : U) (i : Fin r),
    (sections U (((toSheafify (Opens.grothendieckTopology (puncturedLine S))
      (operatorPresheaf ℂ (puncturedLine S) (curveCoefficients S))).app (op U)).hom
        (partialFinite ℂ (puncturedLine S) (curveCoefficients S) C.coordinate U) • s)).val x.val.val i =
      derivWithin (fun t => (sections U s).val t i) (ambientOpen S U) x.val.val -
        ((evaluatedAt hA x.val.val).mulVec ((sections U s).val x.val.val)) i

/-- The original horizontal matrix as an actual map of full native D-modules. -/
structure NativeCurveGaugeSource
    {s : ℕ} (B : Matrix (Fin s) (Fin s) RationalFunctions) (hB : PolesWithin S B)
    (G : Matrix (Fin s) (Fin r) RationalFunctions) (hG : PolesWithin S G)
    (MA : RationalConnectionModuleSource S A hA C)
    (MB : RationalConnectionModuleSource S B hB C) where
  map : MA.object ⟶ MB.object
  sectionValues : ∀ (U : Opens (puncturedLine S)) (v : MA.object.val.obj (op U))
      (x : U) (i : Fin s),
    (MB.sections U ((map.val.app (op U)).hom v)).val x.val.val i =
      ((evaluatedAt hG x.val.val).mulVec ((MA.sections U v).val x.val.val)) i

end MathlibExt.AlgebraicGeometry.NativeRationalCurveModuleModels
