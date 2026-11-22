/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Functor.CoaugmentationIteration
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinder
import MathlibExt.CategoryTheory.NatTrans.PointwiseArrow
import MathlibExt.CategoryTheory.Enriched.PointwiseShapeInstances
import MathlibExt.Topology.Category.CGWH.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# The original native mapping-cylinder telescope of an input coaugmentation

For a native enriched diagram endofunctor `F` with a natural
coaugmentation `η`, this telescope uses the actual transitions `Fⁿ(η_X)`.
Each stage uses the original interval mapping-cylinder functor, its
original second-endpoint source and original contraction retraction.
The chosen natural-number colimit retains every stage leg, all input
maps, every transition equation and its full universal property.

Evaluation uses the genuine pointwise colimit comparison on the same
enriched carrier. No commutation equation for `η` and `F`, telescope
weakness, Omega conclusion or reflection property is an input.
-/

set_option autoImplicit false
noncomputable section
universe u v uA vA uD vD

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.EnrichedCoaugmentationTelescope

section ArrowImages

variable {A : Type uA} {D : Type uD} [Category.{vA} A] [Category.{vD} D]
  {F G : A ⥤ D}

private theorem arrowLeft (a : F ⟶ G) : NatTrans.arrow a ⋙ Arrow.leftFunc = F := rfl

private theorem arrowRight (a : F ⟶ G) : NatTrans.arrow a ⋙ Arrow.rightFunc = G := rfl

private def sourceImage (a : F ⟶ G) {H : Arrow D ⥤ D} (s : Arrow.leftFunc ⟶ H) :
    F ⟶ NatTrans.arrow a ⋙ H :=
  eqToHom (arrowLeft a).symm ≫ Functor.whiskerLeft (NatTrans.arrow a) s

private def targetImage (a : F ⟶ G) {H : Arrow D ⥤ D} (p : H ⟶ Arrow.rightFunc) :
    NatTrans.arrow a ⋙ H ⟶ G :=
  Functor.whiskerLeft (NatTrans.arrow a) p ≫ eqToHom (arrowRight a)

private theorem sourceImage_app (a : F ⟶ G) {H : Arrow D ⥤ D}
    (s : Arrow.leftFunc ⟶ H) (X : A) :
    (sourceImage a s).app X = s.app (Arrow.mk (a.app X)) := by
  change 𝟙 (F.obj X) ≫ s.app (Arrow.mk (a.app X)) = _
  exact Category.id_comp _

private theorem targetImage_app (a : F ⟶ G) {H : Arrow D ⥤ D}
    (p : H ⟶ Arrow.rightFunc) (X : A) :
    (targetImage a p).app X = p.app (Arrow.mk (a.app X)) := by
  change p.app (Arrow.mk (a.app X)) ≫ 𝟙 (G.obj X) = _
  exact Category.comp_id _

private theorem images_factorization (a : F ⟶ G) {H : Arrow D ⥤ D}
    (s : Arrow.leftFunc ⟶ H) (p : H ⟶ Arrow.rightFunc)
    (h : s ≫ p = Arrow.leftToRight) : sourceImage a s ≫ targetImage a p = a := by
  apply NatTrans.ext
  funext X
  rw [NatTrans.comp_app, sourceImage_app, targetImage_app]
  exact congr_app h (Arrow.mk (a.app X))

end ArrowImages

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

private abbrev Carrier (J : Type) [EnrichedCategory PointedCGWH.{u, v} J] :=
  EnrichedFunctorCat PointedCGWH.{u, v} J

attribute [local instance] MonoidalClosed.enrichedCategorySelf

/-- A stage consists of its full original functor and projection to the actual power. -/
structure Stage (F : (Carrier.{u, v} I) ⥤ (Carrier.{u, v} I)) (n : ℕ) where
  /-- The complete native stage functor. -/
  functor : (Carrier.{u, v} I) ⥤ (Carrier.{u, v} I)
  /-- Its complete native projection to the same original endofunctor power. -/
  projection : functor ⟶ Functor.Iteration.iterate F n

variable {F : (Carrier.{u, v} I) ⥤ (Carrier.{u, v} I)} (η : 𝟭 (Carrier.{u, v} I) ⟶ F)

/-- The stage arrow uses its original projection and the original-input transition. -/
def stageArrows {n : ℕ} (d : Stage F n) : (Carrier.{u, v} I) ⥤ Arrow (Carrier.{u, v} I) :=
  NatTrans.arrow (d.projection ≫ Functor.Iteration.inputTransition η n)

/-- Every stage arrow is the actual original whole native arrow at that input. -/
theorem stageArrows_obj {n : ℕ} (d : Stage F n) (X : (Carrier.{u, v} I)) :
    (stageArrows η d).obj X =
      Arrow.mk (d.projection.app X ≫ (Functor.Iteration.inputTransition η n).app X) :=
  rfl

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The next stage is the same original interval pushout on that complete stage arrow. -/
def nextStage {n : ℕ} (d : Stage F n) : Stage F (n + 1) where
  functor := stageArrows η d ⋙ (PointedCGWH.EnrichedIntervalMappingCylinder.functor (I := I))
  projection := targetImage (d.projection ≫ Functor.Iteration.inputTransition η n)
    (PointedCGWH.EnrichedIntervalMappingCylinder.retractionNatTrans (I := I))

/-- The transition is the original second-endpoint source of the same mapping cylinder. -/
def nextTransition {n : ℕ} (d : Stage F n) : d.functor ⟶ (nextStage η d).functor :=
  sourceImage (d.projection ≫ Functor.Iteration.inputTransition η n)
    (PointedCGWH.EnrichedIntervalMappingCylinder.sourceNatTrans (I := I))

omit B in
/-- Original source and contraction maps give the complete factorization. -/
theorem nextTransition_projection {n : ℕ} (d : Stage F n) :
    nextTransition η d ≫ (nextStage η d).projection =
      d.projection ≫ Functor.Iteration.inputTransition η n :=
  images_factorization (d.projection ≫ Functor.Iteration.inputTransition η n)
    (PointedCGWH.EnrichedIntervalMappingCylinder.sourceNatTrans (I := I))
    (PointedCGWH.EnrichedIntervalMappingCylinder.retractionNatTrans (I := I))
    (PointedCGWH.EnrichedIntervalMappingCylinder.fac_natTrans (I := I))

omit B in
/-- Every transition component is the actual same original cylinder source. -/
theorem nextTransition_app {n : ℕ} (d : Stage F n) (X : (Carrier.{u, v} I)) :
    (nextTransition η d).app X =
      PointedCGWH.EnrichedIntervalMappingCylinder.source
        (Arrow.mk (d.projection.app X ≫ (Functor.Iteration.inputTransition η n).app X)) :=
  sourceImage_app (d.projection ≫ Functor.Iteration.inputTransition η n)
    (PointedCGWH.EnrichedIntervalMappingCylinder.sourceNatTrans (I := I)) X

omit B in
/-- Every projection component is the actual original cylinder contraction retraction. -/
theorem nextStage_projection_app {n : ℕ} (d : Stage F n) (X : (Carrier.{u, v} I)) :
    (nextStage η d).projection.app X =
      PointedCGWH.EnrichedIntervalMappingCylinder.retraction
        (Arrow.mk (d.projection.app X ≫ (Functor.Iteration.inputTransition η n).app X)) :=
  targetImage_app (d.projection ≫ Functor.Iteration.inputTransition η n)
    (PointedCGWH.EnrichedIntervalMappingCylinder.retractionNatTrans (I := I)) X

/-- The complete recursive stages start at the actual original identity functor. -/
def stage : ∀ n : ℕ, Stage F n :=
  Nat.rec { functor := 𝟭 _, projection := 𝟙 _ }
    (fun _ previous => nextStage η previous)

/-- The complete transition keeps the actual original map constructed at each stage. -/
def transition (n : ℕ) : (stage η n).functor ⟶ (stage η (n + 1)).functor :=
  nextTransition η (stage η n)

/-- The complete projection keeps the same original power at every stage. -/
def projection (n : ℕ) : (stage η n).functor ⟶ Functor.Iteration.iterate F n :=
  (stage η n).projection

omit B in
/-- The source functor at stage zero is exactly the original identity functor. -/
theorem stage_zero_functor : (stage η 0).functor = 𝟭 (Carrier.{u, v} I) := rfl

omit B in
/-- Its stage-zero projection is exactly the original identity transformation. -/
theorem projection_zero : projection η 0 = 𝟙 (𝟭 (Carrier.{u, v} I)) := rfl

omit B in
/-- The entire recursive successor retains the actual original Arrow and cylinder functors. -/
theorem stage_succ_functor (n : ℕ) :
    (stage η (n + 1)).functor =
      stageArrows η (stage η n) ⋙ (PointedCGWH.EnrichedIntervalMappingCylinder.functor (I := I)) :=
  rfl

omit B in
/-- All stage transitions and projections factor the original `Fⁿ(η_X)` transition. -/
theorem transition_projection (n : ℕ) :
    transition η n ≫ projection η (n + 1) =
      projection η n ≫ Functor.Iteration.inputTransition η n :=
  nextTransition_projection η (stage η n)

omit B in
/-- The complete original factorization holds at every native input object. -/
theorem transition_projection_app (n : ℕ) (X : (Carrier.{u, v} I)) :
    (transition η n).app X ≫ (projection η (n + 1)).app X =
      (projection η n).app X ≫ (Functor.Iteration.inputTransition η n).app X :=
  congr_app (transition_projection η n) X

omit B in
/-- Each successor projection retains the same original contraction retraction. -/
theorem projection_succ_app (n : ℕ) (X : (Carrier.{u, v} I)) :
    (projection η (n + 1)).app X =
      PointedCGWH.EnrichedIntervalMappingCylinder.retraction
        (Arrow.mk ((projection η n).app X ≫
          (Functor.Iteration.inputTransition η n).app X)) :=
  nextStage_projection_app η (stage η n) X

omit B in
/-- Each transition retains the original second endpoint of the same entire stage arrow. -/
theorem transition_app (n : ℕ) (X : (Carrier.{u, v} I)) :
    (transition η n).app X =
      PointedCGWH.EnrichedIntervalMappingCylinder.source
        (Arrow.mk ((projection η n).app X ≫
          (Functor.Iteration.inputTransition η n).app X)) :=
  nextTransition_app η (stage η n) X

/-- The complete original mapping-cylinder stage diagram. -/
def diagram (X : (Carrier.{u, v} I)) : ℕ ⥤ (Carrier.{u, v} I) :=
  Functor.ofSequence (fun n => (transition η n).app X)

omit B in
/-- Every stage is the whole native object of the actual stage functor. -/
theorem diagram_obj (X : (Carrier.{u, v} I)) (n : ℕ) :
    (diagram η X).obj n = (stage η n).functor.obj X := rfl

omit B in
/-- Every adjacent diagram map is the actual original mapping-cylinder transition. -/
theorem diagram_map_succ (X : (Carrier.{u, v} I)) (n : ℕ) :
    (diagram η X).map (homOfLE (Nat.le_add_right n 1)) = (transition η n).app X :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- Every original native input arrow acts on the entire stage diagram. -/
def diagramMap {X Y : (Carrier.{u, v} I)} (f : X ⟶ Y) : diagram η X ⟶ diagram η Y :=
  NatTrans.ofSequence (fun n => (stage η n).functor.map f) (fun n => by
    rw [diagram_map_succ, diagram_map_succ]
    exact ((transition η n).naturality f).symm)

/-- The diagram construction retains input identities and compositions. -/
def diagramFunctor : (Carrier.{u, v} I) ⥤ (ℕ ⥤ (Carrier.{u, v} I)) where
  obj := diagram η
  map := diagramMap η
  map_id X := by
    apply NatTrans.ext
    funext n
    exact (stage η n).functor.map_id X
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact (stage η n).functor.map_comp f g

omit B in
/-- Every diagram-map component is the original full stage-functor map. -/
theorem diagramFunctor_map_app {X Y : (Carrier.{u, v} I)} (f : X ⟶ Y) (n : ℕ) :
    ((diagramFunctor η).map f).app n = (stage η n).functor.map f := rfl

omit B in
/-- All original native input maps are natural across every natural-number arrow. -/
theorem diagramMap_naturality {X Y : (Carrier.{u, v} I)} (f : X ⟶ Y)
    {n m : ℕ} (a : n ⟶ m) :
    (diagram η X).map a ≫ (stage η m).functor.map f =
      (stage η n).functor.map f ≫ (diagram η Y).map a :=
  (diagramMap η f).naturality a

/-- The full original stage projections compare the entire diagram to actual `Fⁿ(η_X)`. -/
def diagramProjection (X : (Carrier.{u, v} I)) :
    diagram η X ⟶ Functor.Iteration.inputDiagram η X :=
  NatTrans.ofSequence (fun n => (projection η n).app X) (fun n => by
    rw [diagram_map_succ, Functor.Iteration.inputDiagram_map_succ]
    exact transition_projection_app η n X)

omit B in
/-- Every projection component retains its original complete stage map. -/
theorem diagramProjection_app (X : (Carrier.{u, v} I)) (n : ℕ) :
    (diagramProjection η X).app n = (projection η n).app X := rfl

omit B in
/-- The original projections are natural on every complete input arrow. -/
theorem diagramProjection_naturality {X Y : (Carrier.{u, v} I)} (f : X ⟶ Y) :
    diagramMap η f ≫ diagramProjection η Y =
      diagramProjection η X ≫ Functor.Iteration.inputDiagramMap η f := by
  apply NatTrans.ext
  funext n
  exact (projection η n).naturality f

/-- The complete stage projection is natural in all native inputs. -/
def diagramProjectionNatTrans : diagramFunctor η ⟶ Functor.Iteration.inputDiagramFunctor η where
  app := diagramProjection η
  naturality {_X _Y} f := diagramProjection_naturality η f

omit B in
private theorem pointedNatColimits : HasColimitsOfShape ℕ PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
    change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
    infer_instance
  infer_instance

attribute [local instance] pointedNatColimits

/-- The telescope uses the actual chosen colimit of the entire original diagram. -/
def telescopeFunctor : (Carrier.{u, v} I) ⥤ (Carrier.{u, v} I) := diagramFunctor η ⋙ colim

/-- Its object is the same literal original chosen native colimit. -/
def telescope (X : (Carrier.{u, v} I)) : (Carrier.{u, v} I) := (telescopeFunctor η).obj X

/-- Every stage leg is the original chosen colimit inclusion. -/
def leg (X : (Carrier.{u, v} I)) (n : ℕ) : (stage η n).functor.obj X ⟶ telescope η X :=
  colimit.ι (diagram η X) n

omit B in
/-- The full colimit condition retains every natural-number arrow. -/
theorem transition_leg (X : (Carrier.{u, v} I)) {n m : ℕ} (a : n ⟶ m) :
    (diagram η X).map a ≫ leg η X m = leg η X n :=
  colimit.w (diagram η X) a

omit B in
/-- Every original native input map commutes with every chosen stage leg. -/
theorem leg_naturality {X Y : (Carrier.{u, v} I)} (f : X ⟶ Y) (n : ℕ) :
    leg η X n ≫ (telescopeFunctor η).map f = (stage η n).functor.map f ≫ leg η Y n :=
  colimit.ι_map (diagramMap η f) n

/-- The original input enters the telescope by its actual stage-zero leg. -/
def unit : 𝟭 (Carrier.{u, v} I) ⟶ telescopeFunctor η where
  app X := leg η X 0
  naturality {_X _Y} f := (leg_naturality η f 0).symm

omit B in
/-- Every unit is precisely the chosen leg at the unchanged original stage zero. -/
theorem unit_app (X : (Carrier.{u, v} I)) : (unit η).app X = leg η X 0 := rfl

/-- Every whole native cocone gives the original chosen telescope descent. -/
def desc (X : (Carrier.{u, v} I)) (c : Cocone (diagram η X)) : telescope η X ⟶ c.pt :=
  colimit.desc (diagram η X) c

omit B in
/-- The actual descent retains all original cocone legs. -/
theorem leg_desc (X : (Carrier.{u, v} I)) (c : Cocone (diagram η X)) (n : ℕ) :
    leg η X n ≫ desc η X c = c.ι.app n :=
  colimit.ι_desc c n

omit B in
/-- All original chosen legs jointly determine a map from the same telescope. -/
theorem hom_ext (X Y : (Carrier.{u, v} I)) (f g : telescope η X ⟶ Y)
    (h : ∀ n : ℕ, leg η X n ≫ f = leg η X n ≫ g) : f = g :=
  colimit.hom_ext h

omit B in
/-- Every telescope leg is natural on every complete native enriched Hom object. -/
theorem leg_uncurried_naturality (X : (Carrier.{u, v} I)) (n : ℕ) (a b : I) :
    MonoidalClosed.uncurry (((stage η n).functor.obj X).toEnrichedFunctor.map a b) ≫
        component (leg η X n) b =
      (component (leg η X n) a ⊗ₘ 𝟙 (a ⟶[PointedCGWH.{u, v}] b)) ≫
        MonoidalClosed.uncurry ((telescope η X).toEnrichedFunctor.map a b) :=
  (leg η X n).uncurriedNaturality a b

/-- The chosen colimit of the same original input-transition diagram. -/
def iterationColimitFunctor : (Carrier.{u, v} I) ⥤ (Carrier.{u, v} I) :=
  Functor.Iteration.inputDiagramFunctor η ⋙ colim

/-- The complete original projections induce the same chosen-colimit comparison. -/
def toIterationColimit : telescopeFunctor η ⟶ iterationColimitFunctor η :=
  Functor.whiskerRight (diagramProjectionNatTrans η) colim

omit B in
/-- Every comparison leg is the original projection followed by the original power-colimit leg. -/
theorem leg_toIterationColimit (X : (Carrier.{u, v} I)) (n : ℕ) :
    leg η X n ≫ (toIterationColimit η).app X =
      (projection η n).app X ≫ colimit.ι (Functor.Iteration.inputDiagram η X) n :=
  colimit.ι_map (diagramProjection η X) n

/-- The complete evaluated diagram retains every actual stage and arrow. -/
def evaluatedDiagram (X : (Carrier.{u, v} I)) (a : I) : ℕ ⥤ PointedCGWH.{u, v} :=
  diagram η X ⋙ evaluation a

/-- Evaluation identifies the same original chosen native colimit with its pointwise colimit. -/
def evaluationIso (X : (Carrier.{u, v} I)) (a : I) :
    (telescope η X).toEnrichedFunctor.obj a ≅ colimit (evaluatedDiagram η X a) :=
  preservesColimitIso (evaluation a) (diagram η X)

omit B in
/-- Every forward evaluation comparison retains the actual original stage leg. -/
theorem evaluated_leg_hom (X : (Carrier.{u, v} I)) (a : I) (n : ℕ) :
    (evaluation a).map (leg η X n) ≫ (evaluationIso η X a).hom =
      colimit.ι (evaluatedDiagram η X a) n :=
  ι_preservesColimitIso_hom (evaluation a) (diagram η X) n

omit B in
/-- The inverse comparison retains those same chosen stage legs. -/
theorem evaluated_leg_inv (X : (Carrier.{u, v} I)) (a : I) (n : ℕ) :
    colimit.ι (evaluatedDiagram η X a) n ≫ (evaluationIso η X a).inv =
      (evaluation a).map (leg η X n) :=
  ι_preservesColimitIso_inv (evaluation a) (diagram η X) n

/-- The complete native evaluation comparison is natural in every original input. -/
def evaluationNatIso (a : I) :
    telescopeFunctor η ⋙ evaluation a ≅
      (diagramFunctor η ⋙ (Functor.whiskeringRight ℕ (Carrier.{u, v} I) PointedCGWH.{u, v}).obj
        (evaluation a)) ⋙ colim :=
  Functor.associator (diagramFunctor η) colim (evaluation a) ≪≫
    Functor.isoWhiskerLeft (diagramFunctor η) (preservesColimitNatIso (evaluation a)) ≪≫
      (Functor.associator (diagramFunctor η)
        ((Functor.whiskeringRight ℕ (Carrier.{u, v} I) PointedCGWH.{u, v}).obj (evaluation a))
        colim).symm

omit B in
/-- The full forward natural comparison has the actual chosen pointwise-colimit map. -/
theorem evaluationNatIso_hom_app (a : I) (X : (Carrier.{u, v} I)) :
    (evaluationNatIso η a).hom.app X = (evaluationIso η X a).hom := by
  change 𝟙 _ ≫ ((preservesColimitIso (evaluation a) (diagram η X)).hom ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]
  rfl

omit B in
/-- Its full inverse retains the same original inverse pointwise-colimit map. -/
theorem evaluationNatIso_inv_app (a : I) (X : (Carrier.{u, v} I)) :
    (evaluationNatIso η a).inv.app X = (evaluationIso η X a).inv := by
  change 𝟙 _ ≫ ((preservesColimitIso (evaluation a) (diagram η X)).inv ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]
  rfl

end PointedCGWH.EnrichedCoaugmentationTelescope
