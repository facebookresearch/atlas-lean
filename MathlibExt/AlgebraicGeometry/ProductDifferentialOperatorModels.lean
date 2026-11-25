/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProjectiveExponentialSectionModels
public import MathlibExt.AlgebraicGeometry.PulledBetaRingModels
public import MathlibExt.AlgebraicGeometry.NativeOrdinaryDifferentialRepresentations
public import MathlibExt.CategoryTheory.NativeTwoOperatorModuleViews
public import MathlibExt.AlgebraicGeometry.GeometricDModuleFiltrations

/-!
# Actual complex product structure and full independent X/P operators

The product is the original X times native P. Both original projections
are holomorphic for the source product complex structure. Full finite X
and P operators act by the actual corresponding holomorphic slice; the
ordinary ring maps and their beta maps retain every original section.
Their commuting multiplication square fixes the X/P bimodule views.

Source: DK1311.2374v2 Sections4.10,8.2,9.1;
Mathlib56a005 native product, ring pullback and finite operators, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProductDifferentialOperatorModels

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open ProjectiveExponentialSectionModels NativeIndDifferentialContexts
open PulledBetaRingModels NativeOrdinaryDifferentialRepresentations
open DifferentialOperatorSheaves
open MathlibExt.CategoryTheory.NativeTwoOperatorModuleViews
open scoped Manifold ContDiff

variable (n : ℕ) (X : Type) [TopologicalSpace X]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) X]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ X]
  [ProjectiveComplexSource]

abbrev ProductSpace := TopCat.of (X × ProjectiveLine)

def xProjection : ProductSpace X ⟶ TopCat.of X := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
def pProjection : ProductSpace X ⟶ TopCat.of ProjectiveLine := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

/-- For a complex manifold $X$ of dimension $n$ (and the complex structure on $\mathbb{P}^1$ given
by `ProjectiveComplexSource`), a complex manifold structure on $X \times \mathbb{P}^1$: charts
modelled on $\mathbb{C}^{n+1}$ with holomorphic transition maps, for which both projections, to $X$
and to $\mathbb{P}^1$, are holomorphic. -/
class ProductComplexSource where
  [charts : ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates (n + 1))
    (X × ProjectiveLine)]
  [manifold : IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates (n + 1)) ∞
    (X × ProjectiveLine)]
  firstHolomorphic : ContMDiff 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates (n + 1))
    𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞
      (Prod.fst : X × ProjectiveLine → X)
  secondHolomorphic : ContMDiff 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates (n + 1))
    𝓘(ℂ, ProjectiveCoordinates) ∞ (Prod.snd : X × ProjectiveLine → ProjectiveLine)

attribute [instance_reducible, instance] ProductComplexSource.charts
attribute [instance] ProductComplexSource.manifold

variable [ProductComplexSource n X]
  [HasSheafify (Opens.grothendieckTopology X) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology ProjectiveLine) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology (X × ProjectiveLine)) RingCat.{0}]

def rectangle (U : Opens X) (V : Opens ProjectiveLine) : Opens (ProductSpace X) :=
  ⟨(U : Set X) ×ˢ V, U.isOpen.prod V.isOpen⟩

abbrev XRing := analyticDifferentialRing n X
abbrev PRing := analyticDifferentialRing 1 ProjectiveLine
abbrev FullProductRing := analyticDifferentialRing (n + 1) (X × ProjectiveLine)
abbrev ProjectedXRing := pullbackRing (xProjection X) (XRing n X)
abbrev ProjectedPRing := pullbackRing (pProjection X) PRing

def xOperatorSection (φ : ProjectedXRing n X ⟶ FullProductRing n X)
    (U : Opens X) (V : Opens ProjectiveLine)
    (P : finiteOperatorRing ℂ X (analyticCoefficients n X) U) :
    (FullProductRing n X).obj.obj (op (rectangle X U V)) :=
  (φ.hom.app (op (rectangle X U V))).hom
    (pullbackSection (xProjection X) (XRing n X) U
      (GeometricDModuleFiltrations.operatorValue
        (TemperedDistributionSectionModels.ComplexCoordinates n) X P)
      (rectangle X U V) (fun _ h => h.1))

def pOperatorSection (φ : ProjectedPRing X ⟶ FullProductRing n X)
    (U : Opens X) (V : Opens ProjectiveLine)
    (P : finiteOperatorRing ℂ ProjectiveLine (analyticCoefficients 1 ProjectiveLine) V) :
    (FullProductRing n X).obj.obj (op (rectangle X U V)) :=
  (φ.hom.app (op (rectangle X U V))).hom
    (pullbackSection (pProjection X) PRing V
      (GeometricDModuleFiltrations.operatorValue ProjectiveCoordinates ProjectiveLine P)
      (rectangle X U V) (fun _ h => h.2))

variable (O : StructureModuleSource (X × ProjectiveLine) (analyticCoefficients (n + 1)
    (X × ProjectiveLine)))

/-- Full ordinary operator embeddings are fixed on every actual product slice and original section. -/
structure ProductOperatorSource where
  xMap : ProjectedXRing n X ⟶ FullProductRing n X
  pMap : ProjectedPRing X ⟶ FullProductRing n X
  xSlice : ∀ (U : Opens X) (V : Opens ProjectiveLine)
    (g : (analyticCoefficients (n + 1) (X × ProjectiveLine)).obj (op (rectangle X U V)))
    (p : V), (analyticCoefficients n X).obj (op U)
  pSlice : ∀ (U : Opens X) (V : Opens ProjectiveLine)
    (g : (analyticCoefficients (n + 1) (X × ProjectiveLine)).obj (op (rectangle X U V)))
    (x : U), (analyticCoefficients 1 ProjectiveLine).obj (op V)
  xSliceValue : ∀ (U : Opens X) (V : Opens ProjectiveLine)
    (g : (analyticCoefficients (n + 1) (X × ProjectiveLine)).obj (op (rectangle X U V)))
    (x : U) (p : V), (xSlice U V g p).val x = g.val ⟨(x.val, p.val), x.property, p.property⟩
  pSliceValue : ∀ (U : Opens X) (V : Opens ProjectiveLine)
    (g : (analyticCoefficients (n + 1) (X × ProjectiveLine)).obj (op (rectangle X U V)))
    (x : U) (p : V), (pSlice U V g x).val p = g.val ⟨(x.val, p.val), x.property, p.property⟩
  xAction : ∀ (U : Opens X) (V : Opens ProjectiveLine)
      (P : finiteOperatorRing ℂ X (analyticCoefficients n X) U)
      (g : (analyticCoefficients (n + 1) (X × ProjectiveLine)).obj (op (rectangle X U V)))
      (x : U) (p : V),
    (O.sections (rectangle X U V) (xOperatorSection n X xMap U V P •
      ((O.sections (rectangle X U V)).symm g))).val ⟨(x.val, p.val), x.property, p.property⟩ =
        (P.val.val ⟨U, le_refl U⟩ (xSlice U V g p)).val x
  pAction : ∀ (U : Opens X) (V : Opens ProjectiveLine)
      (P : finiteOperatorRing ℂ ProjectiveLine (analyticCoefficients 1 ProjectiveLine) V)
      (g : (analyticCoefficients (n + 1) (X × ProjectiveLine)).obj (op (rectangle X U V)))
      (x : U) (p : V),
    (O.sections (rectangle X U V) (pOperatorSection n X pMap U V P •
      ((O.sections (rectangle X U V)).symm g))).val ⟨(x.val, p.val), x.property, p.property⟩ =
        (P.val.val ⟨V, le_refl V⟩ (pSlice U V g x)).val p

end MathlibExt.AlgebraicGeometry.ProductDifferentialOperatorModels
