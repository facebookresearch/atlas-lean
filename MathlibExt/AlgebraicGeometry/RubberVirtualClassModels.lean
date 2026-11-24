/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RubberPOTSourceCharts
public import MathlibExt.AlgebraicGeometry.LiFamilySourceDescent
public import MathlibExt.AlgebraicGeometry.POTActualConeCoordinates
public import MathlibExt.AlgebraicGeometry.SchemeStackModuleModels
public import MathlibExt.AlgebraicGeometry.StackVirtualPullbacks
public import MathlibExt.AlgebraicGeometry.PixtonChowPolynomialModels
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Actual Li rubber virtual classes and independent double ramification cycles

The source retains the full marked-curve, lifted-map Cech and actual
torus Lie construction, together with its global family/frame descent.
One map of actual affine-point cochain presheaves identifies this source
with the bundle-stack diagram on all affine points and arrows.
The obstruction presentation is a real affine cotangent comparison.
Its actual global closed conical embedding is
fixed on every cone function and tangent arrow in all coefficient rings.
The virtual class is the native specialization/cone-push/inverse-bundle
projection recipe. DR is its actual proper-DM epsilon push.

Pixton's constant term is constructed independently from the actual
graph/cotangent-line Chow sum. The comparison preserves2^(-g).
Source: JPPZ arXiv:1602.04705v2, Definition0.2.4/Theorem1;
Jun Li arXiv:math/0110113v1, Sections1--2; Manolache arXiv:0805.2065v2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.RubberVirtualClassModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpandedTargetChainGeometry
open StandardRelativeExpansionModels RubberMapFamilies RubberModuliStackModels
open StackCycleGeometry StackCycleRelations StackChowGroups StackBundleCones StackVirtualPullbacks
open AffineConeAtlas
attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [Field k]
  (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)

structure Point where
  model : SchemeStackModuleModels.Model (Over.mk (𝟙 (Spec (.of k))))
  scope : FiniteTypeArtin k model.stack
  classes : CycleClassData D K model.stack scope
  fundamental : FundamentalCycleData D model.stack scope 0

def virtualDimension (g n : ℕ) : ℤ := 2 * (g : ℤ) - 3 + n

variable
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k)) (Q : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
  {g n : ℕ} (a : Fin n → ℤ) (B : RubberModuliModel O P Q R S (g := g) a)
  (Z : Point D K)

/-- The virtual-class input for rubber maps. The comparisons `comparison` and
`globalComparison` identify the Li deformation complex with the obstruction-theory complex as
complexes (locally in the derived category, and by one global cochain map); they are not required
to match the obstruction assignments, so this records the weaker complex-level comparison. -/
structure VirtualData where
  structural : StackHom B.stack Z.model.stack
  bundle : VectorBundleStack B.stack
  rank : bundle.virtualRank = -virtualDimension g n
  star : ConditionStar structural bundle
  bundleScope : FiniteTypeArtin k bundle.total
  coneScope : FiniteTypeArtin k star.cone.total
  presentation : letI := star.cone.chart.geometry.algebra;
    ConePresentation star.cone.chart.presentation
  obstruction : letI := star.cone.chart.geometry.algebra;
    IsObstructionTheory presentation
  coefficients : POTAffineModuleFrames.Coefficients
    star.cone.chart.geometry.source.U star.cone.chart.geometry.sourcePoint
  frame : letI := star.cone.chart.geometry.algebra;
    POTAffineModuleFrames.Frame bundle star.cone.chart.geometry.source.U
      star.cone.chart.geometry.sourcePoint star.cone.chart.presentation presentation coefficients
  normalizedCone : letI := star.cone.chart.geometry.algebra;
    POTActualConeCoordinates.Model star.cone bundle star.embedding star.cone.chart presentation coefficients frame
  source : RubberPOTSourceCharts.Chart O P Q R S a B
    star.cone.chart.geometry.source.U star.cone.chart.geometry.sourcePoint
  comparison : letI := star.cone.chart.geometry.algebra;
    DerivedCategory.Q.obj (RubberPOTSourceCharts.complex O P Q R S a B source) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (RubberPOTSourceCharts.ringMap O P Q R S a B source)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (LiFiniteComplexPresentations.complexAt
              (POTConeFunctorModels.tangentMatrix star.cone.chart.presentation presentation)
              Γ(star.cone.chart.geometry.source.U.left, ⊤) 2))
  globalSource : LiFamilySourceDescent.Descent
    (O := O) (P := P) (D := Q) (R := R) (S := S) (a := a) (B := B)
  globalComparison : LiFamilySourceDescent.BundleBinding bundle globalSource
  recipe : VirtualPullbackRecipe D K B.finiteType Z.scope bundle bundleScope star.cone coneScope star.embedding

def virtualClass (V : VirtualData D K O P Q R S a B Z) :
    RationalChowGroup D K B.stack B.finiteType (virtualDimension g n) :=
  rationalMap (chowRegrade D K B.stack B.finiteType (by rw [V.rank]; simp))
    (StackVirtualPullbacks.virtualClass V.recipe 0 Z.fundamental Z.classes)

variable (M : StableCurveStackModels.StableCurveStackModel (k := k) g n)
  (E : EpsilonData O P Q R S a B M)

structure ProperEpsilon where
  proper : DMProperModel D K B.finiteType M.finiteType E.map
  push : RationalPushData D K B.finiteType M.finiteType E.map proper

def doubleRamificationCycle (V : VirtualData D K O P Q R S a B Z)
    (F : ProperEpsilon D K O P Q R S a B M E) :
    RationalChowGroup D K M.stack M.finiteType (virtualDimension g n) :=
  F.push.map _ (virtualClass D K O P Q R S a B Z V)

variable (L : PixtonChowPolynomialModels.GraphCatalogue g n)
  (G : PixtonChowPolynomialModels.CatalogueGeometry (D := D) (K := K) L M)
  (C : PixtonChowPolynomialModels.PixtonPolynomial (D := D) (K := K) L M G a g)

def pixtonCycle : RationalChowGroup D K M.stack M.finiteType (virtualDimension g n) :=
  rationalMap (chowRegrade D K M.stack M.finiteType (by dsimp [virtualDimension]; omega))
    (PixtonChowPolynomialModels.pixtonConstant L M G C)

def Comparison (V : VirtualData D K O P Q R S a B Z)
    (F : ProperEpsilon D K O P Q R S a B M E) : Prop :=
  doubleRamificationCycle D K O P Q R S a B Z M E V F =
    (2 : ℚ) ^ (-(g : ℤ)) • pixtonCycle D K a M L G C

end MathlibExt.AlgebraicGeometry.RubberVirtualClassModels
