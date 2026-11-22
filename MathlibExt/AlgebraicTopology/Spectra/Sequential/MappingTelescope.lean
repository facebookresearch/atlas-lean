/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.Evaluation
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinder
import MathlibExt.CategoryTheory.NatTrans.PointwiseArrow
import MathlibExt.Topology.Category.CGWH.Colimits
import MathlibExt.CategoryTheory.Enriched.PointwiseShapeInstances

/-!
# The actual ordered mapping telescope on the original spectrum carrier

The original ordered loop stages and unit maps are replaced successively
by the SAME original interval mapping cylinders. Every stage is a full
native functor, with its original projection to the original iterate and
the exact full transition factorization. Their whole Nat diagram gives
the actual chosen colimit telescope. The initial original spectrum map,
all original stage legs, input maps, naturalities and complete colimit
universal property are retained. No homotopy-group/telescope-weakness law
is supplied; those source8.8 properties remain separate proof obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F G : C ⥤ D}

/-- The entire original source functor, including its maps and laws, is retained. -/
private theorem arrowLeft (a : F ⟶ G) : NatTrans.arrow a ⋙ Arrow.leftFunc = F := rfl

/-- The entire original target functor, including its maps and laws, is retained. -/
private theorem arrowRight (a : F ⟶ G) : NatTrans.arrow a ⋙ Arrow.rightFunc = G := rfl

/-- The whole factorization source uses the actual full Arrow functor and its original source. -/
private def sourceImage (a : F ⟶ G) {H : Arrow D ⥤ D} (s : Arrow.leftFunc ⟶ H) :
    F ⟶ NatTrans.arrow a ⋙ H :=
  eqToHom (arrowLeft a).symm ≫ CategoryTheory.Functor.whiskerLeft (NatTrans.arrow a) s

/-- The whole factorization target uses the actual full Arrow functor and its original target. -/
private def targetImage (a : F ⟶ G) {H : Arrow D ⥤ D} (p : H ⟶ Arrow.rightFunc) :
    NatTrans.arrow a ⋙ H ⟶ G :=
  CategoryTheory.Functor.whiskerLeft (NatTrans.arrow a) p ≫ eqToHom (arrowRight a)

/-- The complete original factorization source component is retained on every original object. -/
private theorem sourceImage_app (a : F ⟶ G) {H : Arrow D ⥤ D}
    (s : Arrow.leftFunc ⟶ H) (X : C) :
    (sourceImage a s).app X = s.app (Arrow.mk (a.app X)) := by
  change 𝟙 (F.obj X) ≫ s.app (Arrow.mk (a.app X)) = _
  exact Category.id_comp _

/-- The complete original factorization target component is retained on every original object. -/
private theorem targetImage_app (a : F ⟶ G) {H : Arrow D ⥤ D}
    (p : H ⟶ Arrow.rightFunc) (X : C) :
    (targetImage a p).app X = p.app (Arrow.mk (a.app X)) := by
  change p.app (Arrow.mk (a.app X)) ≫ 𝟙 (G.obj X) = _
  exact Category.comp_id _

/-- A genuine original Arrow factorization gives the exact whole original NatTrans factorization. -/
private theorem factorization (a : F ⟶ G) {H : Arrow D ⥤ D}
    (s : Arrow.leftFunc ⟶ H) (p : H ⟶ Arrow.rightFunc)
    (h : s ≫ p = Arrow.leftToRight) : sourceImage a s ≫ targetImage a p = a := by
  apply NatTrans.ext
  funext X
  rw [NatTrans.comp_app, sourceImage_app, targetImage_app]
  exact congr_app h (Arrow.mk (a.app X))

end PointedCGWH.SequentialSpectrum.MappingTelescope

namespace PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.OrderedLoop
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/--
A stage retains the whole original native functor and its full projection to the original
iterate.
-/
structure Stage (n : ℕ) where
  /-- The complete native stage functor. -/
  functor : PointedCGWH.SequentialSpectrum.{u, v} ⥤ PointedCGWH.SequentialSpectrum.{u, v}
  /-- The original entire stage projection. -/
  projection : functor ⟶ iterate n

/-- The actual stage Arrow is the original projection followed by the original next unit. -/
def stageArrows {n : ℕ} (d : Stage.{u, v} n) :
    PointedCGWH.SequentialSpectrum.{u, v} ⥤ Arrow PointedCGWH.SequentialSpectrum.{u, v} :=
  NatTrans.arrow (d.projection ≫ iterateUnit n)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The next full native stage uses the SAME original interval mapping-cylinder functor. -/
def nextStage {n : ℕ} (d : Stage.{u, v} n) : Stage.{u, v} (n + 1) where
  functor := stageArrows d ⋙ PointedCGWH.EnrichedIntervalMappingCylinder.functor
  projection := targetImage (d.projection ≫ iterateUnit n)
    PointedCGWH.EnrichedIntervalMappingCylinder.retractionNatTrans

/-- The full next-stage transition is the SAME original second-endpoint mapping-cylinder source. -/
def nextTransition {n : ℕ} (d : Stage.{u, v} n) : d.functor ⟶ (nextStage d).functor :=
  sourceImage (d.projection ≫ iterateUnit n)
    PointedCGWH.EnrichedIntervalMappingCylinder.sourceNatTrans

omit B in
/-- The entire next-stage transition retains its exact original projection and original unit. -/
theorem nextTransition_projection {n : ℕ} (d : Stage.{u, v} n) :
    nextTransition d ≫ (nextStage d).projection = d.projection ≫ iterateUnit n :=
  factorization (d.projection ≫ iterateUnit n)
    PointedCGWH.EnrichedIntervalMappingCylinder.sourceNatTrans
    PointedCGWH.EnrichedIntervalMappingCylinder.retractionNatTrans
    PointedCGWH.EnrichedIntervalMappingCylinder.fac_natTrans

/--
The actual recursive stages start at the original spectrum and use the original mapping
cylinders.
-/
def stage : ∀ n : ℕ, Stage.{u, v} n
  | 0 => { functor := 𝟭 _, projection := 𝟙 _ }
  | n + 1 => nextStage (stage n)

/-- Every complete original stage transition is the literal transition constructed at that stage. -/
def transition (n : ℕ) : (stage.{u, v} n).functor ⟶ (stage (n + 1)).functor :=
  nextTransition (stage n)

/-- The whole original stage projection keeps the SAME original iteration functor. -/
def projection (n : ℕ) : (stage.{u, v} n).functor ⟶ iterate n := (stage n).projection

omit B in
/-- All complete original projection/transition/unit data satisfy the exact whole factorization. -/
theorem transition_projection (n : ℕ) :
    transition.{u, v} n ≫ projection (n + 1) = projection n ≫ iterateUnit n :=
  nextTransition_projection (stage n)

omit B in
/--
Every original stage has its literal original interval-pushout successor, with every input
map.
-/
theorem stage_succ_functor (n : ℕ) :
    (stage.{u, v} (n + 1)).functor =
      stageArrows (stage n) ⋙ PointedCGWH.EnrichedIntervalMappingCylinder.functor := rfl

/-- The full original mapping-cylinder stages form the actual entire Nat diagram. -/
def diagram (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    ℕ ⥤ PointedCGWH.SequentialSpectrum.{u, v} :=
  Functor.ofSequence (fun n => (transition n).app X)

omit B in
/-- Every actual original telescope stage is the original full stage object. -/
theorem diagram_obj (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (diagram X).obj n = (stage n).functor.obj X := rfl

omit B in
/-- Each complete original successive map is the actual original mapping-cylinder source. -/
theorem diagram_map_succ (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (diagram X).map (homOfLE (Nat.le_add_right n 1)) = (transition n).app X :=
  Functor.ofSequence_map_homOfLE_succ _ n

/--
Every original spectrum Arrow gives a whole original natural transformation of the stage
diagrams.
-/
def diagramMap {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    diagram X ⟶ diagram Y :=
  NatTrans.ofSequence (fun n => (stage n).functor.map f) (fun n => by
    rw [diagram_map_succ, diagram_map_succ]
    exact ((transition n).naturality f).symm)

/--
The entire original mapping-cylinder diagram construction is functorial on all original input
maps.
-/
def diagramFunctor : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ PointedCGWH.SequentialSpectrum.{u, v}) where
  obj := diagram
  map := diagramMap
  map_id X := by
    apply NatTrans.ext
    funext n
    exact (stage n).functor.map_id X
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact (stage n).functor.map_comp f g

omit B in
/-- Every full original stage diagram map is the original full stage-functor map. -/
theorem diagramFunctor_map_app
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    (diagramFunctor.map f).app n = (stage n).functor.map f := rfl

/-- The complete original stage projections form the full comparison to the original R iteration. -/
def diagramProjection (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    diagram X ⟶ iterationDiagram X :=
  NatTrans.ofSequence (fun n => (projection n).app X) (fun n => by
    rw [diagram_map_succ, iterationDiagram_map_succ]
    exact congr_app (transition_projection n) X)

omit B in
/-- The actual original pointed category has the Nat colimits used by this source construction. -/
private theorem pointedNatColimits : HasColimitsOfShape ℕ PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
    change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
    infer_instance
  infer_instance

attribute [local instance] pointedNatColimits

/--
The actual full original mapping telescope is the chosen colimit of its entire original
diagram.
-/
def telescopeFunctor : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    PointedCGWH.SequentialSpectrum.{u, v} := diagramFunctor ⋙ colim

/--
Its complete original point is the literal original chosen colimit, with no alternative
object.
-/
def telescope (X : PointedCGWH.SequentialSpectrum.{u, v}) : PointedCGWH.SequentialSpectrum.{u, v} :=
  telescopeFunctor.obj X

/-- Every original stage leg is retained as the actual original chosen colimit leg. -/
def leg (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (stage n).functor.obj X ⟶ telescope X := colimit.ι (diagram X) n

omit B in
/-- Every arbitrary original Nat transition retains the full actual chosen colimit equation. -/
theorem transition_leg (X : PointedCGWH.SequentialSpectrum.{u, v})
    {n m : ℕ} (f : n ⟶ m) : (diagram X).map f ≫ leg X m = leg X n :=
  colimit.w (diagram X) f

omit B in
/-- All original spectrum maps commute with ALL original chosen stage legs. -/
theorem leg_naturality {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    leg X n ≫ telescopeFunctor.map f = (stage n).functor.map f ≫ leg Y n :=
  colimit.ι_map (diagramMap f) n

/-- The initial original spectrum map is the actual stage-zero leg of the original telescope. -/
def unit : 𝟭 PointedCGWH.SequentialSpectrum.{u, v} ⟶ telescopeFunctor where
  app X := leg X 0
  naturality _ _ f := (leg_naturality f 0).symm

/-- Every actual original full cocone gives the actual original unique telescope descent. -/
def desc (X : PointedCGWH.SequentialSpectrum.{u, v}) (c : Cocone (diagram X)) :
    telescope X ⟶ c.pt := colimit.desc (diagram X) c

omit B in
/-- Every original telescope descent retains ALL original full cocone legs. -/
theorem leg_desc (X : PointedCGWH.SequentialSpectrum.{u, v})
    (c : Cocone (diagram X)) (n : ℕ) : leg X n ≫ desc X c = c.ι.app n :=
  colimit.ι_desc c n

omit B in
/--
The complete original universal property uniquely determines maps out of the actual telescope.
-/
theorem hom_ext (X Y : PointedCGWH.SequentialSpectrum.{u, v}) (f g : telescope X ⟶ Y)
    (h : ∀ n : ℕ, leg X n ≫ f = leg X n ≫ g) : f = g :=
  colimit.hom_ext h

end PointedCGWH.SequentialSpectrum.MappingTelescope
