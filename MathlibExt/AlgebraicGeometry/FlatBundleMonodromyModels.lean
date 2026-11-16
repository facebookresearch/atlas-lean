/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HarmonicReconstructionInterfaces
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Actual flat-bundle monodromy through horizontal sheaf stalks

The groupoid is the native path-homotopy fundamental groupoid. Its
objects are the actual coefficient-sheaf stalks. Transport is fixed on
every path lying in every actual local constant frame by the native
germ coordinates. Functor composition fixes the transport on arbitrary
paths. The physical fibre comparison evaluates actual horizontal germs
in the original native bundle; no unrelated representation is supplied.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FlatBundleMonodromyModels

open CategoryTheory Opposite TopologicalSpace
open KahlerClassGeometry SmoothHarmonicBundleGeometry HarmonicHorizontalSheaves
open HarmonicReconstructionInterfaces
open scoped Manifold ContDiff

variable {M : Type} [TopologicalSpace M]

/-- The actual native coefficient-sheaf stalk, preserving its complex module structure. -/
def coefficientStalk (G : CoefficientSheaf (M := M)) (x : M) : ModuleCat.{0} ℂ := TopCat.Presheaf.stalk (X := TopCat.of M) G.obj x

/-- An actual local constant frame fixes all sections and their restrictions. -/
structure LocalCoefficientFrame (G : CoefficientSheaf (M := M)) (U : Opens M) (r : ℕ) where
  coordinates : ∀ (V : Opens M), V ≤ U → G.obj.obj (op V) ≃ₗ[ℂ] LocallyConstant V (FiberCoordinates r)
  restriction : ∀ (V W : Opens M) (a : V ≤ U) (b : W ≤ U) (c : W ≤ V)
    (s : G.obj.obj (op V)) (x : W),
      coordinates W b ((G.obj.map (homOfLE c).op).hom s) x =
        coordinates V a s ⟨x.val, c x.property⟩

/-- Stalk coordinates evaluate the actual native germ of every local section. -/
structure LocalStalkCoordinates {G : CoefficientSheaf (M := M)} {U : Opens M} {r : ℕ}
    (F : LocalCoefficientFrame G U r) (x : M) (hx : x ∈ U) where
  iso : coefficientStalk G x ≃ₗ[ℂ] FiberCoordinates r
  normalized : ∀ (V : Opens M) (a : V ≤ U) (hV : x ∈ V) (s : G.obj.obj (op V)),
    iso ((TopCat.Presheaf.germ (X := TopCat.of M) G.obj V x hV).hom s) = F.coordinates V a s ⟨x, hV⟩

/-- The actual groupoid source objects are the literal sheaf stalks. -/
structure StalkFunctorModel (G : CoefficientSheaf (M := M)) where
  functor : FundamentalGroupoid M ⥤ ModuleCat.{0} ℂ
  objects : ∀ x : M, functor.obj ⟨x⟩ = coefficientStalk G x

/-- Actual path-class transport uses native functor action and only the literal object equality transports. -/
def stalkPathMap {G : CoefficientSheaf (M := M)} (F : StalkFunctorModel G) {x y : M}
    (p : Path x y) : coefficientStalk G x ⟶ coefficientStalk G y :=
  eqToHom (F.objects x).symm ≫
    F.functor.map (show (⟨x⟩ : FundamentalGroupoid M) ⟶ ⟨y⟩ from Path.Homotopic.Quotient.mk p) ≫
    eqToHom (F.objects y)

/-- Every actual local frame fixes transport on every path within its open set. -/
structure StalkMonodromySource (G : CoefficientSheaf (M := M)) extends StalkFunctorModel G where
  normalized : ∀ (U : Opens M) (r : ℕ) (F : LocalCoefficientFrame G U r)
    (x y : M) (hx : x ∈ U) (hy : y ∈ U)
    (Cx : LocalStalkCoordinates F x hx) (Cy : LocalStalkCoordinates F y hy)
    (p : Path x y), Set.range p ⊆ U → ∀ v : coefficientStalk G x,
      Cy.iso ((stalkPathMap toStalkFunctorModel p).hom v) = Cx.iso v

variable {n : ℕ} [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  {r : ℕ} (B : SmoothComplexBundle n M r) (A : SmoothConnection B)
  [SectionCalculus B A.value] [HasSheafify (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)]

/-- The actual raw horizontal section enters its associated sheaf through the native sheafification unit. -/
def horizontalSheafSection (U : Opens M) (s : horizontalModule B A.value U) :
    (horizontalSheaf B A.value).obj.obj (op U) :=
  ((toSheafify (Opens.grothendieckTopology M) (horizontalPresheaf B A.value)).app (op U)).hom s

/-- The physical fibre map evaluates every genuine horizontal section germ in its actual original bundle fibre. -/
structure FlatStalkRealization (x : M) where
  iso : coefficientStalk (horizontalSheaf B A.value) x ≃ₗ[ℂ] B.core.Fiber x
  normalized : ∀ (U : Opens M) (hx : x ∈ U) (s : horizontalModule B A.value U),
    iso ((TopCat.Presheaf.germ (X := TopCat.of M) (horizontalSheaf B A.value).obj U x hx).hom (horizontalSheafSection B A U s)) = s.val ⟨x, hx⟩

/-- Actual fibre transport is the same stalk monodromy conjugated by the actual horizontal evaluation maps. -/
def physicalPathTransport
    (F : StalkMonodromySource (horizontalSheaf B A.value)) {x y : M}
    (Cx : FlatStalkRealization B A x) (Cy : FlatStalkRealization B A y) (p : Path x y) :
    B.core.Fiber x →ₗ[ℂ] B.core.Fiber y :=
  Cy.iso.toLinearMap.comp ((stalkPathMap F.toStalkFunctorModel p).hom.comp Cx.iso.symm.toLinearMap)

end MathlibExt.AlgebraicGeometry.FlatBundleMonodromyModels
