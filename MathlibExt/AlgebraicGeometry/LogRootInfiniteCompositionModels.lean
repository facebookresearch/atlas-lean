/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogRootFiniteCompositionModels
public import MathlibExt.AlgebraicGeometry.RelativeStackImageModels

/-!
# Native infinite-root composition fixed by finite coefficients

The total functors are the actual native strong root arrows followed by
the literal base-change total view. A comparison over the original log
square is fixed by the identity underlying scheme map, every finite
comparison cell and the native projection naturality. Finite comparison
cells themselves are fixed on every original root line.
Source: Talpo--Vistoli1410.1164v2, Sections3--6.
Constructing the composite of canonical arrows for arbitrary root
realizations is left to a separate development: it needs realizations whose
evaluated root comparisons are coherent over the whole tower, which they do
not record.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LogRootInfiniteCompositionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.StackCycleGeometry _root_.AlgebraicGeometry.StackFibreModels
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootStacks FiniteRootTowers
open KatoChartCoefficientModels LogRootSourceModels LogRootCompositionModels
open CanonicalLogRootArrowModels LogRootFiniteCompositeCoordinates LogRootFiniteCompositionModels
open InfiniteRootPreservationModels RelativeStackImageModels

variable [InverseImageTheory.{0}] (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
  {X Y Z : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y) (g : EtaleLogSchemes.Hom Y Z)
  (h : EtaleLogSchemes.Hom X Z)
  (RX : RootRealization X D I) (RY : RootRealization Y D I) (RZ : RootRealization Z D I)
  [HasBaseChanges RY.infinite.stack] [∀ n : Exponent, HasBaseChanges (RY.finite n).stack]
  [HasBaseChanges RZ.infinite.stack] [∀ n : Exponent, HasBaseChanges (RZ.finite n).stack]
  (F : FiniteArrow I D f RX RY) (G : FiniteArrow I D g RY RZ) (H : FiniteArrow I D h RX RZ)
  (AF : InfiniteArrow I D f RX RY F) (AG : InfiniteArrow I D g RY RZ G)
  (AH : InfiniteArrow I D h RX RZ H) (S : OriginalSquare f g h)

/-- Native total functor of a root arrow, with the actual scheme base map. -/
def rootTotalMap {U V : LogScheme.{0}} (a : EtaleLogSchemes.Hom U V)
    (RU : RootRealization U D I) (RV : RootRealization V D I)
    [HasBaseChanges RV.infinite.stack] [∀ n : Exponent, HasBaseChanges (RV.finite n).stack]
    (A : FiniteArrow I D a RU RV) (B : InfiniteArrow I D a RU RV A) :
    Total RU.infinite.stack ⥤ Total RV.infinite.stack :=
  totalMap B.morphism ⋙ RootEtaleRestrictions.totalView a.map RV.infinite.stack

/-- Actual infinite composition on a parameter, including the native equality reindexing. -/
def infiniteCompositeFunctor (T : Over X.scheme) :
    RX.infinite.stack.Fibre T ⥤ RZ.infinite.stack.Fibre ((Over.map h.map).obj T) :=
  component AF.morphism T ⋙ component AG.morphism ((Over.map f.map).obj T) ⋙
    (RZ.infinite.stack.toPseudofunctor.map (parameterArrow f g h S T).op.toLoc).toFunctor

/-- Projection of this actual infinite composite agrees with the actual finite composite. -/
def compositeProjectionMap (T : Over X.scheme) (n : Exponent)
    (x : RX.infinite.stack.Fibre T) :=
  let Ty := (Over.map f.map).obj T
  let Tf := (Over.map g.map).obj Ty
  let a := parameterArrow f g h S T
  let p := (RZ.infinite.projection n)
  let xF := (component AF.morphism T).obj x
  let xG := (component AG.morphism Ty).obj xF
  let e := (RZ.finite n).stack.toPseudofunctor.map a.op.toLoc
  (Cat.Hom.toNatIso (p.naturality a.op.toLoc)).hom.app xG ≫
    e.toFunctor.map ((AG.finite Ty n).hom.app xF) ≫
    e.toFunctor.map ((G.functor Ty n).map ((AF.finite T n).hom.app x))

/-- All comparison cells are the actual original root maps, normalized by every finite root coefficient. -/
structure InfiniteComposition where
  finite : FiniteComposition I D f RX RY g h RZ F G H S
  component : ∀ T : Over X.scheme,
    StackCycleGeometry.component AH.morphism T ≅
      infiniteCompositeFunctor I D f g h RX RY RZ F G AF AG S T
  finite_normalization : ∀ (T : Over X.scheme) (n : Exponent) (x : RX.infinite.stack.Fibre T),
    (StackCycleGeometry.component (RZ.infinite.projection n) ((Over.map h.map).obj T)).map
      ((component T).hom.app x) ≫ compositeProjectionMap I D f g h RX RY RZ F G AF AG S T n x =
    (AH.finite T n).hom.app x ≫ (finite.comparison T n).hom.app
      ((StackCycleGeometry.component (RX.infinite.projection n) T).obj x)
  total : rootTotalMap I D h RX RZ H AH ≅
    rootTotalMap I D f RX RY F AF ⋙ rootTotalMap I D g RY RZ G AG
  base_normalization : ∀ (T : Over X.scheme) (x : RX.infinite.stack.Fibre T),
    HEq ((total.hom.app ⟨T, x⟩).base) (parameterArrow f g h S T)
  component_normalization : ∀ (T : Over X.scheme) (x : RX.infinite.stack.Fibre T),
    HEq ((total.hom.app ⟨T, x⟩).fiber) ((component T).hom.app x)

end MathlibExt.AlgebraicGeometry.LogRootInfiniteCompositionModels
