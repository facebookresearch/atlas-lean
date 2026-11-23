/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalQK0ComparisonCompatibility
public import MathlibExt.CategoryTheory.Monoidal.CoreAdditiveFunctorMap
public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMap
public import MathlibExt.KTheory.Exact.K0.Functor

/-!
# The canonical completed-Core K0 dictionary on every component

The actual completed-Core exact-functor map retains both original object
images. Its actual realization induces the map on all original connected
components. The canonical positive-first K0 difference commutes with that
map, by the original vertex dictionary and exact K0.map generator law.
The source and target category object/Hom universes remain independent.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory

attribute [local instance] CategoryTheory.MonoidalActionCategory.diagonalAction

universe uC vC uD vD

namespace AlgebraicKTheory.OriginalQK0Comparison

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

omit [ExactCategory C] [ExactCategory D] [F.IsExact] in
private def originalCompletedCoreComponentsMapComputed :
    ZerothHomotopy (BasedSplitExactQLoop.completedCoreSpace (C := C)) →
      ZerothHomotopy (BasedSplitExactQLoop.completedCoreSpace (C := D)) :=
  let f := CategoryTheory.realizedNerveFunctorMap
    (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F)
  ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (f x))
    (fun {_ _} p => ZerothHomotopy.sound (p.map f.continuous))

omit [ExactCategory C] [ExactCategory D] [F.IsExact] in
/-- The actual completed-Core functor induces the map on every original realized component. -/
public def completedCoreComponentsMap :
    ZerothHomotopy (BasedSplitExactQLoop.completedCoreSpace (C := C)) →
      ZerothHomotopy (BasedSplitExactQLoop.completedCoreSpace (C := D)) :=
  originalCompletedCoreComponentsMapComputed F

omit [ExactCategory C] [ExactCategory D] [F.IsExact] in
private theorem originalCompletedCoreComponentsMapRepresentative
    (x : BasedSplitExactQLoop.completedCoreSpace (C := C)) :
    completedCoreComponentsMap F (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (CategoryTheory.realizedNerveFunctorMap
        (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F) x) := rfl

omit [ExactCategory C] [ExactCategory D] [F.IsExact] in
/-- Representatives map through the actual original completed-Core realization map. -/
public theorem completedCoreComponentsMap_mk
    (x : BasedSplitExactQLoop.completedCoreSpace (C := C)) :
    completedCoreComponentsMap F (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (CategoryTheory.realizedNerveFunctorMap
        (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F) x) :=
  originalCompletedCoreComponentsMapRepresentative F x

private theorem originalCanonicalCoreK0NaturalityComputed
    (c : ZerothHomotopy (BasedSplitExactQLoop.completedCoreSpace (C := C))) :
    canonicalCoreComponentsK0 (C := D) (completedCoreComponentsMap F c) =
      K0.map F (canonicalCoreComponentsK0 (C := C) c) := by
  obtain ⟨a, ha⟩ := canonicalCoreComponents_vertex_surjective (C := C) c
  let v : BasedSplitExactQLoop.completedCoreSpace (C := C) :=
    SSet.realizedVertex
      (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max uC vC}))
      (ComposableArrows.mk₀ a)
  let b := (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F).obj a
  have hVertex := CategoryTheory.realizedNerveFunctorMap_vertex
    (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F) a
  have hMap : completedCoreComponentsMap F (ZerothHomotopy.mk v) =
      ZerothHomotopy.mk (SSet.realizedVertex
        (X := (nerve (SInverse (Core D) (Core D)) : SSet.{max uD vD}))
        (ComposableArrows.mk₀ b)) :=
    (completedCoreComponentsMap_mk F v).trans (congrArg ZerothHomotopy.mk hVertex)
  have hObject := CategoryTheory.CoreLocalizationComparison.completedCoreFunctor_obj F a
  have hNumerator : b.of.1.of = F.obj a.of.1.of :=
    (congrArg (fun q : SInverse (Core D) (Core D) => q.of.1.of) hObject).trans (by rfl)
  have hDenominator : b.of.2.of = F.obj a.of.2.of :=
    (congrArg (fun q : SInverse (Core D) (Core D) => q.of.2.of) hObject).trans (by rfl)
  have hTarget : canonicalCoreComponentsK0 (C := D)
      (completedCoreComponentsMap F (ZerothHomotopy.mk v)) =
        K0.mk (F.obj a.of.1.of) - K0.mk (F.obj a.of.2.of) :=
    (congrArg (canonicalCoreComponentsK0 (C := D)) hMap).trans
      ((canonicalCoreComponentsK0_mk (C := D) b).trans
        (congrArg₂ (fun (X Y : D) => K0.mk X - K0.mk Y) hNumerator hDenominator))
  have hSource : K0.map F (canonicalCoreComponentsK0 (C := C) (ZerothHomotopy.mk v)) =
      K0.mk (F.obj a.of.1.of) - K0.mk (F.obj a.of.2.of) :=
    (congrArg (K0.map F) (canonicalCoreComponentsK0_mk (C := C) a)).trans
      ((map_sub (K0.map F) (K0.mk a.of.1.of) (K0.mk a.of.2.of)).trans
        (congrArg₂ (fun (X Y : K0 D) => X - Y)
          (K0.map_mk F a.of.1.of) (K0.map_mk F a.of.2.of)))
  exact (congrArg (fun d => canonicalCoreComponentsK0 (C := D)
      (completedCoreComponentsMap F d)) ha.symm).trans
    (hTarget.trans (hSource.symm.trans
      (congrArg (fun d => K0.map F (canonicalCoreComponentsK0 (C := C) d)) ha)))

/-- The original canonical K0 dictionary commutes with every exact functor on every component. -/
public theorem canonicalCoreComponentsK0_naturality
    (c : ZerothHomotopy (BasedSplitExactQLoop.completedCoreSpace (C := C))) :
    canonicalCoreComponentsK0 (C := D) (completedCoreComponentsMap F c) =
      K0.map F (canonicalCoreComponentsK0 (C := C) c) :=
  originalCanonicalCoreK0NaturalityComputed F c

end AlgebraicKTheory.OriginalQK0Comparison

end
