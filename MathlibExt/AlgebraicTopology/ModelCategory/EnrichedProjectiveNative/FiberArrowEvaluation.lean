/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FiberEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHModelStructure
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SerreFiberLoop

/-!
# Entire original chosen-fiber Arrow comparisons under evaluation

Both original projection arrows are retained as full Arrow objects. The
comparison to the literal native fiber keeps the original total endpoint
and the original chosen zero-component comparison. All four hom/inverse
components and both whole Arrow-functor natural isomorphisms are proved.

Caller-chosen fibers use their original cones and universal properties.
The selected original fiber functors also have their own whole comparisons;
they are not replaced by a chosen-family alias. No stable model is used.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CGWH.limits MonoidalClosed
open HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- The entire caller-chosen total-projection Arrow has the literal native fiber Arrow Iso. -/
def chosenFiberTotalArrowIso (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    Arrow.mk ((EnrichedFunctorCat.evaluation a).map s.fst) ≅
      Arrow.mk (PointedCGWH.StrictFiberGeometry.fiberToTotal
        ((EnrichedFunctorCat.evaluation a).map f)) :=
  Arrow.isoMk' _ _ (chosenFiberComponentIso a f s hs)
    (Iso.refl ((EnrichedFunctorCat.evaluation a).obj X)) (by
      rw [Iso.refl_hom, Category.comp_id]
      exact chosenFiberComponentIso_hom_fst a f s hs)

/-- The entire caller-chosen collapse Arrow retains the actual original zero-component Iso. -/
def chosenFiberZeroArrowIso (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    Arrow.mk ((EnrichedFunctorCat.evaluation a).map s.snd) ≅
      Arrow.mk (PointedCGWH.StrictFiberGeometry.fiberToPoint
        ((EnrichedFunctorCat.evaluation a).map f)) :=
  Arrow.isoMk' _ _ (chosenFiberComponentIso a f s hs) (zeroComponentPointIso a)
    (chosenFiberComponentIso_hom_snd a f s hs)

/-- The full forward total-Arrow source map is the original chosen fiber evaluation Iso. -/
theorem chosenFiberTotalArrowIso_hom_left (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberTotalArrowIso a f s hs).hom.left = (chosenFiberComponentIso a f s hs).hom := rfl

/-- The full forward total-Arrow target map is the identity of the original total component. -/
theorem chosenFiberTotalArrowIso_hom_right (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberTotalArrowIso a f s hs).hom.right =
      𝟙 ((EnrichedFunctorCat.evaluation a).obj X) := rfl

/-- The full inverse total-Arrow source map is the actual chosen fiber inverse. -/
theorem chosenFiberTotalArrowIso_inv_left (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberTotalArrowIso a f s hs).inv.left = (chosenFiberComponentIso a f s hs).inv := rfl

/-- The full inverse total-Arrow target map is the same original total identity. -/
theorem chosenFiberTotalArrowIso_inv_right (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberTotalArrowIso a f s hs).inv.right =
      𝟙 ((EnrichedFunctorCat.evaluation a).obj X) := rfl

/-- The full forward collapse-Arrow source map is the original chosen fiber evaluation Iso. -/
theorem chosenFiberZeroArrowIso_hom_left (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberZeroArrowIso a f s hs).hom.left = (chosenFiberComponentIso a f s hs).hom := rfl

/-- The full forward collapse-Arrow target map is the original chosen zero-component Iso. -/
theorem chosenFiberZeroArrowIso_hom_right (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberZeroArrowIso a f s hs).hom.right = (zeroComponentPointIso a).hom := rfl

/-- The full inverse collapse-Arrow source map is the original chosen fiber inverse. -/
theorem chosenFiberZeroArrowIso_inv_left (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberZeroArrowIso a f s hs).inv.left = (chosenFiberComponentIso a f s hs).inv := rfl

/-- The full inverse collapse-Arrow target map is the actual original zero-component inverse. -/
theorem chosenFiberZeroArrowIso_inv_right (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberZeroArrowIso a f s hs).inv.right = (zeroComponentPointIso a).inv := rfl

variable
  (s : ∀ F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A),
    PullbackCone F.hom (zeroTo F.right))
  (hs : ∀ F, IsLimit (s F))

/-- Both complete projection Arrow components commute with evaluation for every chosen fiber. -/
def chosenFiberTotalArrowEvaluationNatIso (a : A) :
    chosenFiberToTotalArrowFunctor s hs ⋙ (EnrichedFunctorCat.evaluation a).mapArrow ≅
      (EnrichedFunctorCat.evaluation a).mapArrow ⋙
        PointedCGWH.StrictFiberGeometry.fiberToTotalArrowFunctor :=
  NatIso.ofComponents (fun F => chosenFiberTotalArrowIso a F.hom (s F) (hs F)) (by
    intro F G q
    apply Arrow.hom_ext
    · change (EnrichedFunctorCat.evaluation a).map ((chosenFiberFunctor s hs).map q) ≫
          (chosenFiberComponentIso a G.hom (s G) (hs G)).hom =
        (chosenFiberComponentIso a F.hom (s F) (hs F)).hom ≫
          PointedCGWH.StrictFiberGeometry.fiberFunctor.map
            ((EnrichedFunctorCat.evaluation a).mapArrow.map q)
      exact (chosenFiberEvaluationNatIso s hs a).hom.naturality q
    · change (EnrichedFunctorCat.evaluation a).map q.left ≫ 𝟙 _ =
        𝟙 _ ≫ (EnrichedFunctorCat.evaluation a).map q.left
      rw [Category.comp_id, Category.id_comp])

/-- Both complete collapse Arrow components retain the same original zero comparison naturally. -/
def chosenFiberZeroArrowEvaluationNatIso (a : A) :
    chosenFiberToZeroArrowFunctor s hs ⋙ (EnrichedFunctorCat.evaluation a).mapArrow ≅
      (EnrichedFunctorCat.evaluation a).mapArrow ⋙
        PointedCGWH.StrictFiberGeometry.fiberToPointArrowFunctor :=
  NatIso.ofComponents (fun F => chosenFiberZeroArrowIso a F.hom (s F) (hs F)) (by
    intro F G q
    apply Arrow.hom_ext
    · change (EnrichedFunctorCat.evaluation a).map ((chosenFiberFunctor s hs).map q) ≫
          (chosenFiberComponentIso a G.hom (s G) (hs G)).hom =
        (chosenFiberComponentIso a F.hom (s F) (hs F)).hom ≫
          PointedCGWH.StrictFiberGeometry.fiberFunctor.map
            ((EnrichedFunctorCat.evaluation a).mapArrow.map q)
      exact (chosenFiberEvaluationNatIso s hs a).hom.naturality q
    · change (EnrichedFunctorCat.evaluation a).map (𝟙 zeroDiagram) ≫
          (zeroComponentPointIso a).hom = (zeroComponentPointIso a).hom ≫ 𝟙 _
      rw [(EnrichedFunctorCat.evaluation a).map_id,
        Category.id_comp, Category.comp_id])

/-- The complete inverse chosen total-Arrow comparison is natural in the entire original square. -/
theorem chosenFiberTotalArrowEvaluationNatIso_inv_naturality (a : A)
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (q : F ⟶ G) :
    ((EnrichedFunctorCat.evaluation a).mapArrow ⋙
      PointedCGWH.StrictFiberGeometry.fiberToTotalArrowFunctor).map q ≫
        (chosenFiberTotalArrowEvaluationNatIso s hs a).inv.app G =
      (chosenFiberTotalArrowEvaluationNatIso s hs a).inv.app F ≫
        (chosenFiberToTotalArrowFunctor s hs ⋙ (EnrichedFunctorCat.evaluation a).mapArrow).map q :=
  (chosenFiberTotalArrowEvaluationNatIso s hs a).inv.naturality q

/-- The complete inverse chosen collapse-Arrow comparison is natural in the
entire original square. -/
theorem chosenFiberZeroArrowEvaluationNatIso_inv_naturality (a : A)
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (q : F ⟶ G) :
    ((EnrichedFunctorCat.evaluation a).mapArrow ⋙
      PointedCGWH.StrictFiberGeometry.fiberToPointArrowFunctor).map q ≫
        (chosenFiberZeroArrowEvaluationNatIso s hs a).inv.app G =
      (chosenFiberZeroArrowEvaluationNatIso s hs a).inv.app F ≫
        (chosenFiberToZeroArrowFunctor s hs ⋙ (EnrichedFunctorCat.evaluation a).mapArrow).map q :=
  (chosenFiberZeroArrowEvaluationNatIso s hs a).inv.naturality q

omit s hs in
/-- The selected original total-projection Arrow functor has its own complete evaluation Iso. -/
def fiberTotalArrowEvaluationNatIso (a : A) :
    fiberToTotalArrowFunctor (A := A) ⋙ (EnrichedFunctorCat.evaluation a).mapArrow ≅
      (EnrichedFunctorCat.evaluation a).mapArrow ⋙
        PointedCGWH.StrictFiberGeometry.fiberToTotalArrowFunctor :=
  NatIso.ofComponents
    (fun F => chosenFiberTotalArrowIso a F.hom (fiberCone F.hom) (fiberConeIsLimit F.hom)) (by
      intro F G q
      apply Arrow.hom_ext
      · change (EnrichedFunctorCat.evaluation a).map (fiberFunctor.map q) ≫ _ = _
        exact (fiberEvaluationNatIso a).hom.naturality q
      · change (EnrichedFunctorCat.evaluation a).map q.left ≫ 𝟙 _ =
          𝟙 _ ≫ (EnrichedFunctorCat.evaluation a).map q.left
        rw [Category.comp_id, Category.id_comp])

omit s hs in
/-- The selected original collapse Arrow functor retains its own whole zero-component Iso. -/
def fiberZeroArrowEvaluationNatIso (a : A) :
    fiberToZeroArrowFunctor (A := A) ⋙ (EnrichedFunctorCat.evaluation a).mapArrow ≅
      (EnrichedFunctorCat.evaluation a).mapArrow ⋙
        PointedCGWH.StrictFiberGeometry.fiberToPointArrowFunctor :=
  NatIso.ofComponents
    (fun F => chosenFiberZeroArrowIso a F.hom (fiberCone F.hom) (fiberConeIsLimit F.hom)) (by
      intro F G q
      apply Arrow.hom_ext
      · change (EnrichedFunctorCat.evaluation a).map (fiberFunctor.map q) ≫ _ = _
        exact (fiberEvaluationNatIso a).hom.naturality q
      · change (EnrichedFunctorCat.evaluation a).map (𝟙 zeroDiagram) ≫
            (zeroComponentPointIso a).hom = (zeroComponentPointIso a).hom ≫ 𝟙 _
        rw [(EnrichedFunctorCat.evaluation a).map_id, Category.id_comp, Category.comp_id])

/-- Coordinate collapse weakness agrees with the literal native fiber collapse. -/
theorem chosenFiberCollapse_component_weak_iff (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    weakEquivalences PointedCGWH.{u, v} ((EnrichedFunctorCat.evaluation a).map s.snd) ↔
      weakEquivalences PointedCGWH.{u, v}
        (PointedCGWH.StrictFiberGeometry.fiberToPoint ((EnrichedFunctorCat.evaluation a).map f)) :=
  (weakEquivalences PointedCGWH.{u, v}).arrow_mk_iso_iff
    (chosenFiberZeroArrowIso a f s hs)

/-- The exact original coordinate-collapse premise gives the actual CGWH strict-fiber weakness. -/
theorem chosenFiberCollapse_component_CGWH_weak (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s)
    (h : weakEquivalences PointedCGWH.{u, v} ((EnrichedFunctorCat.evaluation a).map s.snd)) :
    CGWH.weakHomotopyEquivalences
      (CGWH.strictFiberToPoint ((EnrichedFunctorCat.evaluation a).map f).right
        ((EnrichedFunctorCat.evaluation a).obj Y).hom) := by
  have hw := (chosenFiberCollapse_component_weak_iff a f s hs).mp h
  change weakEquivalences CGWH.{u, v}
    (CGWH.strictFiberToPoint ((EnrichedFunctorCat.evaluation a).map f).right
      ((EnrichedFunctorCat.evaluation a).obj Y).hom)
  let t := PointedCGWH.StrictFiberGeometry.fiberToPoint ((EnrichedFunctorCat.evaluation a).map f)
  have ht : WeakEquivalence t := (HomotopicalAlgebra.weakEquivalence_iff t).mpr hw
  have hright : WeakEquivalence t.right := (PointedCGWH.weakEquivalence_iff t).mp ht
  exact (HomotopicalAlgebra.weakEquivalence_iff t.right).mp hright


/-- The actual chosen fiber collapse at a coordinate gives original successor loop weakness. -/
theorem chosenFiber_component_ihomSphereOne_weak (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s)
    [Fibration ((EnrichedFunctorCat.evaluation a).map f)]
    (h : weakEquivalences PointedCGWH.{u, v} ((EnrichedFunctorCat.evaluation a).map s.snd)) :
    weakEquivalences PointedCGWH.{u, v}
      ((ihom PointedCGWH.sphereOne).map ((EnrichedFunctorCat.evaluation a).map f)) :=
  PointedCGWH.FiberGeometry.ihomSphereOne_weak_of_strictFiber_weak_collapse
    ((EnrichedFunctorCat.evaluation a).map f)
    (chosenFiberCollapse_component_CGWH_weak a f s hs h)


end HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
