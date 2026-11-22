/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.StrictFiber
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StrictFiber
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Evaluating the same chosen original spectrum fiber

The original enriched pointwise limit construction preserves each chosen
fiber cone under actual evaluation. Its original zero component is compared
with the literal pointed native point by its proved universal property.
The evaluated cone, with that same zero comparison, is again a limit.

This constructs the entire isomorphism to the literal original native
CGWH strict fiber, preserving both projections and the exact original
chosen fiber point. It applies to an arbitrary caller-chosen fiber cone,
not just to a newly selected pullback. Every nonidentity Arrow map is
preserved. The complete fiber functors and both projection Arrow functors
are naturally isomorphic, with all four isomorphism components identified.

Only actual original limits and original pointed maps enter the proof.
No stable-model or fiber-collapse assumption occurs.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CGWH.limits MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- The original zero-diagram component is identified with the literal pointed native point. -/
def zeroComponentPointIso (a : A) :
    (EnrichedFunctorCat.evaluation a).obj (zeroDiagram (A := A)) ≅
      PointedCGWH.StrictFiberGeometry.pointObject :=
  (initialDiagram_component_isZero a).isTerminal.uniqueUpToIso
    PointedCGWH.StrictFiberGeometry.pointObjectIsTerminal

/-- The original zero-to-spectrum component is exactly the chosen zero comparison and basepoint. -/
theorem zeroTo_component_characteristic (a : A)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (EnrichedFunctorCat.evaluation a).map (zeroTo X) =
      (zeroComponentPointIso a).hom ≫
        PointedCGWH.StrictFiberGeometry.fromPoint
          ((EnrichedFunctorCat.evaluation a).obj X) :=
  (initialDiagram_component_isZero a).isInitial.hom_ext _ _

/-- The inverse zero comparison retains the actual original zero-to-spectrum component. -/
theorem zeroTo_component_inverse_characteristic (a : A)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (zeroComponentPointIso a).inv ≫ (EnrichedFunctorCat.evaluation a).map (zeroTo X) =
      PointedCGWH.StrictFiberGeometry.fromPoint ((EnrichedFunctorCat.evaluation a).obj X) := by
  rw [zeroTo_component_characteristic, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Original maps to the original zero retain the literal pointed collapse after its chosen Iso. -/
theorem toZero_component_characteristic (a : A)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (EnrichedFunctorCat.evaluation a).map (toZero X) ≫ (zeroComponentPointIso a).hom =
      PointedCGWH.StrictFiberGeometry.toPoint ((EnrichedFunctorCat.evaluation a).obj X) :=
  PointedCGWH.StrictFiberGeometry.pointObjectIsTerminal.hom_ext _ _

/-- Actual original evaluation preserves the full chosen fiber cospan. -/
theorem evaluation_preserves_fiber (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    PreservesLimit (cospan f (zeroTo Y)) (EnrichedFunctorCat.evaluation a) := inferInstance

/-- Evaluate the caller's entire actual original fiber cone. -/
abbrev evaluatedChosenCone (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) :
    PullbackCone ((EnrichedFunctorCat.evaluation a).map f)
      ((EnrichedFunctorCat.evaluation a).map (zeroTo Y)) :=
  s.map (EnrichedFunctorCat.evaluation a)

/-- The caller's evaluated cone has the actual original pointwise limit universal property. -/
def evaluatedChosenConeIsLimit (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    IsLimit (evaluatedChosenCone a f s) :=
  (PullbackCone.isLimitMapConeEquiv s (EnrichedFunctorCat.evaluation a)).1
    (isLimitOfPreserves (EnrichedFunctorCat.evaluation a) hs)

/-- The original evaluated legs satisfy the square after the actual chosen zero comparison. -/
theorem evaluated_point_condition (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) :
    (EnrichedFunctorCat.evaluation a).map s.fst ≫ (EnrichedFunctorCat.evaluation a).map f =
      ((EnrichedFunctorCat.evaluation a).map s.snd ≫ (zeroComponentPointIso a).hom) ≫
        PointedCGWH.StrictFiberGeometry.fromPoint ((EnrichedFunctorCat.evaluation a).obj Y) := by
  have h := (evaluatedChosenCone a f s).condition
  change (EnrichedFunctorCat.evaluation a).map s.fst ≫
      (EnrichedFunctorCat.evaluation a).map f =
    (EnrichedFunctorCat.evaluation a).map s.snd ≫
      (EnrichedFunctorCat.evaluation a).map (zeroTo Y) at h
  rw [zeroTo_component_characteristic, ← Category.assoc] at h
  exact h

/-- Retain the original evaluated object and total leg, and the original chosen zero Iso. -/
abbrev evaluatedPointCone (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) :
    PullbackCone ((EnrichedFunctorCat.evaluation a).map f)
      (PointedCGWH.StrictFiberGeometry.fromPoint ((EnrichedFunctorCat.evaluation a).obj Y)) :=
  PullbackCone.mk ((EnrichedFunctorCat.evaluation a).map s.fst)
    ((EnrichedFunctorCat.evaluation a).map s.snd ≫ (zeroComponentPointIso a).hom)
    (evaluated_point_condition a f s)

/-- A cone over the literal point has a whole cone over the same original evaluated zero. -/
abbrev pointConeToOriginalZero (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (t : PullbackCone ((EnrichedFunctorCat.evaluation a).map f)
      (PointedCGWH.StrictFiberGeometry.fromPoint ((EnrichedFunctorCat.evaluation a).obj Y))) :
    PullbackCone ((EnrichedFunctorCat.evaluation a).map f)
      ((EnrichedFunctorCat.evaluation a).map (zeroTo Y)) :=
  PullbackCone.mk t.fst (t.snd ≫ (zeroComponentPointIso a).inv) (by
    rw [Category.assoc, zeroTo_component_inverse_characteristic]
    exact t.condition)

/-- The actual evaluated original limit constructs the whole lift from a literal point cone. -/
def evaluatedPointLift (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s)
    (t : PullbackCone ((EnrichedFunctorCat.evaluation a).map f)
      (PointedCGWH.StrictFiberGeometry.fromPoint ((EnrichedFunctorCat.evaluation a).obj Y))) :
    t.pt ⟶ (EnrichedFunctorCat.evaluation a).obj s.pt :=
  (evaluatedChosenConeIsLimit a f s hs).lift (pointConeToOriginalZero a f t)

/-- The lift preserves the entire caller's original evaluated total projection. -/
theorem evaluatedPointLift_fst (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s)
    (t : PullbackCone ((EnrichedFunctorCat.evaluation a).map f)
      (PointedCGWH.StrictFiberGeometry.fromPoint ((EnrichedFunctorCat.evaluation a).obj Y))) :
    evaluatedPointLift a f s hs t ≫ (EnrichedFunctorCat.evaluation a).map s.fst = t.fst :=
  (evaluatedChosenConeIsLimit a f s hs).fac (pointConeToOriginalZero a f t) WalkingCospan.left

/-- The lift preserves the entire caller's original evaluated zero projection. -/
theorem evaluatedPointLift_original_snd (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s)
    (t : PullbackCone ((EnrichedFunctorCat.evaluation a).map f)
      (PointedCGWH.StrictFiberGeometry.fromPoint ((EnrichedFunctorCat.evaluation a).obj Y))) :
    evaluatedPointLift a f s hs t ≫ (EnrichedFunctorCat.evaluation a).map s.snd =
      t.snd ≫ (zeroComponentPointIso a).inv :=
  (evaluatedChosenConeIsLimit a f s hs).fac (pointConeToOriginalZero a f t) WalkingCospan.right

/-- The lift preserves the whole literal point projection through the same chosen zero Iso. -/
theorem evaluatedPointLift_snd (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s)
    (t : PullbackCone ((EnrichedFunctorCat.evaluation a).map f)
      (PointedCGWH.StrictFiberGeometry.fromPoint ((EnrichedFunctorCat.evaluation a).obj Y))) :
    evaluatedPointLift a f s hs t ≫
        ((EnrichedFunctorCat.evaluation a).map s.snd ≫ (zeroComponentPointIso a).hom) = t.snd := by
  rw [← Category.assoc, evaluatedPointLift_original_snd,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The full original evaluated chosen fiber is the actual pullback over the literal point. -/
def evaluatedPointConeIsLimit (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    IsLimit (evaluatedPointCone a f s) := by
  apply PullbackCone.IsLimit.mk (evaluated_point_condition a f s)
  case lift => exact evaluatedPointLift a f s hs
  case fac_left => exact evaluatedPointLift_fst a f s hs
  case fac_right => exact evaluatedPointLift_snd a f s hs
  case uniq =>
    intro t m hm hn
    apply PullbackCone.IsLimit.hom_ext (evaluatedChosenConeIsLimit a f s hs)
    · exact hm.trans (evaluatedPointLift_fst a f s hs t).symm
    · apply (cancel_mono (zeroComponentPointIso a).hom).mp
      change (m ≫ (EnrichedFunctorCat.evaluation a).map s.snd) ≫
          (zeroComponentPointIso a).hom =
        (evaluatedPointLift a f s hs t ≫ (EnrichedFunctorCat.evaluation a).map s.snd) ≫
          (zeroComponentPointIso a).hom
      rw [Category.assoc, Category.assoc, evaluatedPointLift_snd]
      exact hn

/-- The entire caller-chosen original fiber component has its literal native pointed fiber Iso. -/
def chosenFiberComponentIso (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (EnrichedFunctorCat.evaluation a).obj s.pt ≅
      PointedCGWH.StrictFiberGeometry.fiber ((EnrichedFunctorCat.evaluation a).map f) :=
  (evaluatedPointConeIsLimit a f s hs).conePointUniqueUpToIso
    (t := PointedCGWH.StrictFiberGeometry.fiberCone ((EnrichedFunctorCat.evaluation a).map f))
    (PointedCGWH.StrictFiberGeometry.fiberConeIsLimit ((EnrichedFunctorCat.evaluation a).map f))

/-- Its whole forward map retains the caller's original evaluated total projection. -/
theorem chosenFiberComponentIso_hom_fst (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberComponentIso a f s hs).hom ≫
        PointedCGWH.StrictFiberGeometry.fiberToTotal ((EnrichedFunctorCat.evaluation a).map f) =
      (EnrichedFunctorCat.evaluation a).map s.fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp (evaluatedPointConeIsLimit a f s hs)
    (PointedCGWH.StrictFiberGeometry.fiberConeIsLimit ((EnrichedFunctorCat.evaluation a).map f))
    WalkingCospan.left

/-- Its whole forward map retains the caller's original zero leg and that same chosen zero Iso. -/
theorem chosenFiberComponentIso_hom_snd (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberComponentIso a f s hs).hom ≫
        PointedCGWH.StrictFiberGeometry.fiberToPoint ((EnrichedFunctorCat.evaluation a).map f) =
      (EnrichedFunctorCat.evaluation a).map s.snd ≫ (zeroComponentPointIso a).hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp (evaluatedPointConeIsLimit a f s hs)
    (PointedCGWH.StrictFiberGeometry.fiberConeIsLimit ((EnrichedFunctorCat.evaluation a).map f))
    WalkingCospan.right

/-- Its whole inverse map retains the same original evaluated total projection. -/
theorem chosenFiberComponentIso_inv_fst (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberComponentIso a f s hs).inv ≫ (EnrichedFunctorCat.evaluation a).map s.fst =
      PointedCGWH.StrictFiberGeometry.fiberToTotal ((EnrichedFunctorCat.evaluation a).map f) := by
  rw [← chosenFiberComponentIso_hom_fst a f s hs, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Its whole inverse map retains the same original zero projection, with the actual inverse Iso. -/
theorem chosenFiberComponentIso_inv_snd (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberComponentIso a f s hs).inv ≫ (EnrichedFunctorCat.evaluation a).map s.snd =
      PointedCGWH.StrictFiberGeometry.fiberToPoint ((EnrichedFunctorCat.evaluation a).map f) ≫
        (zeroComponentPointIso a).inv := by
  apply (cancel_mono (zeroComponentPointIso a).hom).mp
  rw [Category.assoc, ← chosenFiberComponentIso_hom_snd a f s hs,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The forward Iso preserves the exact original chosen native strict-fiber point. -/
theorem chosenFiberComponentIso_hom_point (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    ((EnrichedFunctorCat.evaluation a).obj s.pt).hom ≫
        (chosenFiberComponentIso a f s hs).hom.right =
      CGWH.strictFiberPoint ((EnrichedFunctorCat.evaluation a).map f).right
        ((EnrichedFunctorCat.evaluation a).obj Y).hom
        ((EnrichedFunctorCat.evaluation a).obj X).hom
        (Under.w ((EnrichedFunctorCat.evaluation a).map f)) :=
  Under.w (chosenFiberComponentIso a f s hs).hom

/-- The inverse Iso preserves the original chosen component basepoint. -/
theorem chosenFiberComponentIso_inv_point (a : A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    CGWH.strictFiberPoint ((EnrichedFunctorCat.evaluation a).map f).right
        ((EnrichedFunctorCat.evaluation a).obj Y).hom
        ((EnrichedFunctorCat.evaluation a).obj X).hom
        (Under.w ((EnrichedFunctorCat.evaluation a).map f)) ≫
        (chosenFiberComponentIso a f s hs).inv.right =
      ((EnrichedFunctorCat.evaluation a).obj s.pt).hom :=
  Under.w (chosenFiberComponentIso a f s hs).inv

/-- The entire chosen-fiber evaluation Iso commutes with every original nonidentity Arrow map. -/
theorem chosenFiberComponentIso_naturality (a : A)
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (q : F ⟶ G)
    (s : PullbackCone F.hom (zeroTo F.right)) (hs : IsLimit s)
    (t : PullbackCone G.hom (zeroTo G.right)) (ht : IsLimit t) :
    (EnrichedFunctorCat.evaluation a).map (chosenFiberMap q s t ht) ≫
        (chosenFiberComponentIso a G.hom t ht).hom =
      (chosenFiberComponentIso a F.hom s hs).hom ≫
        PointedCGWH.StrictFiberGeometry.fiberFunctor.map
          ((EnrichedFunctorCat.evaluation a).mapArrow.map q) := by
  change (EnrichedFunctorCat.evaluation a).map (chosenFiberMap q s t ht) ≫
      (chosenFiberComponentIso a G.hom t ht).hom =
    (chosenFiberComponentIso a F.hom s hs).hom ≫
      PointedCGWH.StrictFiberGeometry.fiberMap ((EnrichedFunctorCat.evaluation a).mapArrow.map q)
  have hFst := PointedCGWH.StrictFiberGeometry.fiberMap_fst
    ((EnrichedFunctorCat.evaluation a).mapArrow.map q)
  change PointedCGWH.StrictFiberGeometry.fiberMap
      ((EnrichedFunctorCat.evaluation a).mapArrow.map q) ≫
      PointedCGWH.StrictFiberGeometry.fiberToTotal ((EnrichedFunctorCat.evaluation a).map G.hom) =
    PointedCGWH.StrictFiberGeometry.fiberToTotal ((EnrichedFunctorCat.evaluation a).map F.hom) ≫
      (EnrichedFunctorCat.evaluation a).map q.left at hFst
  have hSnd := PointedCGWH.StrictFiberGeometry.fiberMap_snd
    ((EnrichedFunctorCat.evaluation a).mapArrow.map q)
  change PointedCGWH.StrictFiberGeometry.fiberMap
      ((EnrichedFunctorCat.evaluation a).mapArrow.map q) ≫
      PointedCGWH.StrictFiberGeometry.fiberToPoint ((EnrichedFunctorCat.evaluation a).map G.hom) =
    PointedCGWH.StrictFiberGeometry.fiberToPoint
      ((EnrichedFunctorCat.evaluation a).map F.hom) at hSnd
  apply PullbackCone.IsLimit.hom_ext
    (PointedCGWH.StrictFiberGeometry.fiberConeIsLimit ((EnrichedFunctorCat.evaluation a).map G.hom))
  · change (_ ≫ (chosenFiberComponentIso a G.hom t ht).hom) ≫
        PointedCGWH.StrictFiberGeometry.fiberToTotal ((EnrichedFunctorCat.evaluation a).map G.hom) =
      (_ ≫ PointedCGWH.StrictFiberGeometry.fiberMap
        ((EnrichedFunctorCat.evaluation a).mapArrow.map q)) ≫
        PointedCGWH.StrictFiberGeometry.fiberToTotal ((EnrichedFunctorCat.evaluation a).map G.hom)
    rw [Category.assoc, chosenFiberComponentIso_hom_fst,
      ← (EnrichedFunctorCat.evaluation a).map_comp, chosenFiberMap_fst,
      (EnrichedFunctorCat.evaluation a).map_comp, Category.assoc,
      hFst, ← Category.assoc,
      chosenFiberComponentIso_hom_fst]
  · change (_ ≫ (chosenFiberComponentIso a G.hom t ht).hom) ≫
        PointedCGWH.StrictFiberGeometry.fiberToPoint ((EnrichedFunctorCat.evaluation a).map G.hom) =
      (_ ≫ PointedCGWH.StrictFiberGeometry.fiberMap
        ((EnrichedFunctorCat.evaluation a).mapArrow.map q)) ≫
        PointedCGWH.StrictFiberGeometry.fiberToPoint ((EnrichedFunctorCat.evaluation a).map G.hom)
    rw [Category.assoc, chosenFiberComponentIso_hom_snd, ← Category.assoc,
      ← (EnrichedFunctorCat.evaluation a).map_comp, chosenFiberMap_snd,
      Category.assoc, hSnd,
      chosenFiberComponentIso_hom_snd]

/-- The selected original map is the map constructed between those same selected limit cones. -/
theorem fiberMap_eq_chosenFiberMap
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (q : F ⟶ G) :
    fiberMap q = chosenFiberMap q (fiberCone F.hom) (fiberCone G.hom) (fiberConeIsLimit G.hom) := by
  apply pullback.hom_ext
  · exact (fiberMap_fst q).trans (chosenFiberMap_fst q _ _ _).symm
  · exact (fiberMap_snd q).trans (chosenFiberMap_snd q _ _ _).symm

/-- The complete original strict-fiber functor commutes with actual evaluation up to whole Iso. -/
def fiberEvaluationNatIso (a : A) :
    fiberFunctor (A := A) ⋙ EnrichedFunctorCat.evaluation a ≅
      (EnrichedFunctorCat.evaluation a).mapArrow ⋙ PointedCGWH.StrictFiberGeometry.fiberFunctor :=
  NatIso.ofComponents
    (fun F => chosenFiberComponentIso a F.hom (fiberCone F.hom) (fiberConeIsLimit F.hom)) (by
      intro F G q
      change (EnrichedFunctorCat.evaluation a).map (fiberMap q) ≫ _ = _
      rw [fiberMap_eq_chosenFiberMap]
      exact chosenFiberComponentIso_naturality a q _ _ _ _)

variable
  (s : ∀ F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A),
    PullbackCone F.hom (zeroTo F.right))
  (hs : ∀ F, IsLimit (s F))

/-- The complete caller-chosen fiber functor has the same literal native evaluation NatIso. -/
def chosenFiberEvaluationNatIso (a : A) :
    chosenFiberFunctor s hs ⋙ EnrichedFunctorCat.evaluation a ≅
      (EnrichedFunctorCat.evaluation a).mapArrow ⋙ PointedCGWH.StrictFiberGeometry.fiberFunctor :=
  NatIso.ofComponents (fun F => chosenFiberComponentIso a F.hom (s F) (hs F)) (by
    intro F G q
    exact chosenFiberComponentIso_naturality a q (s F) (hs F) (s G) (hs G))

/-- Every inverse chosen-functor comparison has complete original Arrow naturality. -/
theorem chosenFiberEvaluationNatIso_inv_naturality (a : A)
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (q : F ⟶ G) :
    PointedCGWH.StrictFiberGeometry.fiberFunctor.map
        ((EnrichedFunctorCat.evaluation a).mapArrow.map q) ≫
        (chosenFiberEvaluationNatIso s hs a).inv.app G =
      (chosenFiberEvaluationNatIso s hs a).inv.app F ≫
        (EnrichedFunctorCat.evaluation a).map ((chosenFiberFunctor s hs).map q) :=
  (chosenFiberEvaluationNatIso s hs a).inv.naturality q

end HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
