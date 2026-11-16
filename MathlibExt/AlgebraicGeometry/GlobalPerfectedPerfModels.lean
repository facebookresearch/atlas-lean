/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GlobalFpPerfectionModels
public import MathlibExt.AlgebraicGeometry.OrdinarySchemeTorModels

/-!
# Actual Perf(Xperf) and its entire original hypercover comparison

Perfection is the global functor already fixed on all affine rings by
the literal Frobenius direct colimit, all affine maps, genuine affine
open restrictions and its universal perfect-source projection.

Each original scheme diagram is first lifted over Fp by its actual
augmentation, then composed with this same global perfection functor.
The categorical perfect limit and comparison are the native all-affine
coefficient-section constructions. All degree, face and degeneracy maps
are the original scheme maps after applying the global functor.

Source: Bhatt--Mathew1807.04725v4, Theorem5.16. No assertion about
base change along an arbitrary affine point is used. Native source
revisions and license/copyright notices are retained in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GlobalPerfectedPerfModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open GeneralArcCoverModels GeneralArcHypercoverModels
open FrobeniusPerfectionModels GlobalFpPerfectionModels
open OrdinarySchemeModuleFamilies OrdinarySchemeDiagramModels OrdinarySchemeTorModels
open OrdinaryConstantCoefficientModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open scoped Simplicial

variable {p : ℕ} {X : FpSchemes p} {J : Type} [Category.{0} J] (H : J ⥤ Over X.left)

/-- The original diagram is over Fp through its literal augmentation to X. -/
def fpDiagram : J ⥤ FpSchemes p where
  obj j := Over.mk (Y := (H.obj j).left) ((H.obj j).hom ≫ X.hom)
  map {i j} f := Over.homMk (H.map f).left (by
    change (H.map f).left ≫ ((H.obj j).hom ≫ X.hom) = (H.obj i).hom ≫ X.hom
    rw [← Category.assoc]
    exact congrArg (fun k : (H.obj i).left ⟶ X.left => k ≫ X.hom) (Over.w (H.map f)))
  map_id j := by
    apply (Over.forget (affine (CommRingCat.of (ZMod p)))).map_injective
    change (H.map (𝟙 j)).left = 𝟙 _
    rw [H.map_id]
    rfl
  map_comp f g := by
    apply (Over.forget (affine (CommRingCat.of (ZMod p)))).map_injective
    change (H.map (f ≫ g)).left = (H.map f).left ≫ (H.map g).left
    rw [H.map_comp]
    rfl

/-- The whole augmentation is its original over-object map, with the original naturality square. -/
def fpAugmentation : fpDiagram H ⟶ (Functor.const J).obj X where
  app j := Over.homMk (H.obj j).hom
  naturality i j f := by
    apply (Over.forget (affine (CommRingCat.of (ZMod p)))).map_injective
    change (H.map f).left ≫ (H.obj j).hom = (H.obj i).hom ≫ 𝟙 X.left
    exact (Over.w (H.map f)).trans (Category.comp_id _).symm

/-- Preserve the actual full augmented diagram as an object of the original native slice. -/
def fpOverDiagram : J ⥤ Over X := Over.lift (fpDiagram H) (fpAugmentation H)

variable {F : FrobeniusSource p} (G : GlobalPerfectionSource F)

/-- Every original object and diagram map is perfected by the same whole global functor. -/
def perfectedDiagram : J ⥤ Over (G.functor.obj X).left :=
  fpOverDiagram H ⋙ Over.post G.functor ⋙
    Over.post (Over.forget (affine (CommRingCat.of (ZMod p))))

/-- The original perfect-complex category on the actual global perfection. -/
def perfectedPerf {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (X : FpSchemes p) : SSet.{1} :=
  OrdinarySchemeModuleFamilies.perf M (G.functor.obj X).left

/-- The same projection gives the canonical actual pullback into the perfected category. -/
def toPerfection {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (X : FpSchemes p) :
    OrdinarySchemeModuleFamilies.perf M X.left ⟶ perfectedPerf G M X :=
  OrdinarySchemeModuleFamilies.perfPullback M (G.projection.app X).left

/-- Every scheme arrow acts by the actual native pullback along its global perfected map. -/
def perfectedPullback {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) {X Y : FpSchemes p} (f : X ⟶ Y) :
    perfectedPerf G M Y ⟶ perfectedPerf G M X :=
  OrdinarySchemeModuleFamilies.perfPullback M (G.functor.map f).left

/-- All categorical hypercover/Čech values are the actual perfected diagram's full native section limit. -/
def perfectedLimit {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) : SSet.{1} := perfLimit (perfectedDiagram H G) M

/-- The actual comparison is original all-affine source reindexing, after the fixed global perfection. -/
def perfectedComparison {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) : perfectedPerf G M X ⟶ perfectedLimit H G M :=
  perfComparison (perfectedDiagram H G) M

/-- Fixed Tor-amplitude uses every actual ordinary module on the global perfected scheme. -/
def perfectedTorPerf {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (T : OrdinaryTorSystem N) (a b : ℤ) : SSet.{1} :=
  torPerf M T (G.functor.obj X).left a b

/-- The same native all-module tests define the full fixed-amplitude diagram limit. -/
def perfectedTorLimit {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (T : OrdinaryTorSystem N) (a b : ℤ) : SSet.{1} :=
  torPerfLimit M T (perfectedDiagram H G) a b

end MathlibExt.AlgebraicGeometry.GlobalPerfectedPerfModels
