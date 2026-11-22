/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.ClosedStages
import MathlibExt.Topology.Category.PointedCGWH.Colimits.ClosedSequential

/-!
# Compact factorization through the actual mapping telescope

The actual chosen telescope cocone remains colimiting after inclusion in
CGWH, compactly generated spaces and TopCat. Both comparison maps retain
every original stage leg and every spectrum-map naturality. Compact maps,
pointed compact maps, cubes and complete relative homotopies factor through
the original closed stages, beyond any prescribed stage. All original
objects, maps, independent universes and choices are retained.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v w uC vC uJ vJ
open CategoryTheory CategoryTheory.Limits Topology HomotopicalAlgebra
open scoped unitInterval Topology.Homotopy

namespace CategoryTheory.Limits
variable {C : Type uC} [Category.{vC} C] {J : Type uJ} [Category.{vJ} J]
  [HasColimitsOfShape J C]

/-- The actual chosen full colimit-point comparisons preserve every complete cocone-map square. -/
private theorem telescope_colimitPointIso_naturality {F G : J ⥤ C} (c : Cocone F) (d : Cocone G)
    (hc : IsColimit c) (hd : IsColimit d) (a : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ j : J, c.ι.app j ≫ g = a.app j ≫ d.ι.app j) :
    colim.map a ≫ ((colimit.isColimit G).coconePointUniqueUpToIso hd).hom =
      ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom ≫ g := by
  apply colimit.hom_ext
  intro j
  have hec : colimit.ι F j ≫ ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom =
      c.ι.app j := IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) hc j
  have hed : colimit.ι G j ≫ ((colimit.isColimit G).coconePointUniqueUpToIso hd).hom =
      d.ι.app j := IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit G) hd j
  rw [colimit.ι_map_assoc, hed, ← Category.assoc, hec]
  exact (hg j).symm

end CategoryTheory.Limits

namespace PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.ClosedSequentialColimit

private theorem pointedNatColimits : HasColimitsOfShape ℕ PointedCGWH.{u, v} := by
  let e : ULift.{v} ℕ ≃o ℕ := ULift.orderIso
  let _ : HasColimitsOfShape (ULift.{v} ℕ) PointedCGWH.{u, v} := inferInstance
  exact hasColimitsOfShape_of_equivalence e.equivalence

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  pointedNatColimits
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The complete actual original chosen telescope cocone evaluated at a level. -/
def levelCocone (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    Cocone (levelDiagram X m) :=
  (PointedCGWH.SequentialSpectrum.evaluation m).mapCocone (colimit.cocone (diagram X))

omit B in
/-- Its whole original point is the same chosen telescope level. -/
theorem levelCocone_pt (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    (levelCocone X m).pt = PointedCGWH.SequentialSpectrum.level (telescope X) m := rfl

omit B in
/-- Every whole level cocone leg is the same original evaluated chosen stage leg. -/
theorem levelCocone_leg (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ) :
    (levelCocone X m).ι.app n = PointedCGWH.SequentialSpectrum.levelMap (leg X n) m := rfl

/-- The whole original evaluated telescope cocone is genuinely colimiting. -/
def levelCoconeIsColimit (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    IsColimit (levelCocone X m) :=
  isColimitOfPreserves (PointedCGWH.SequentialSpectrum.evaluation m)
    (colimit.isColimit (diagram X))

/-- The SAME complete original level cocone is colimiting in CGWH. -/
def levelCoconeCGWHIsColimit (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    IsColimit (pointedToCGWH.mapCocone (levelCocone X m)) :=
  ClosedSequentialColimit.isColimitCGWH (levelCocone X m) (levelCoconeIsColimit X m)

/-- The SAME complete original level cocone is colimiting in compactly generated spaces. -/
def levelCoconeCompactlyGeneratedIsColimit
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    IsColimit ((pointedToCGWH ⋙ CGWH.cgwhToCompactlyGenerated).mapCocone
      (levelCocone X m)) :=
  ClosedSequentialColimit.isColimitCompactlyGenerated (levelCocone X m)
    (levelCoconeIsColimit X m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ)

/-- The SAME complete original level cocone is colimiting in TopCat. -/
def levelCoconeTopIsColimit (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    IsColimit (topFunctor.mapCocone (levelCocone X m)) :=
  ClosedSequentialColimit.isColimitTop (levelCocone X m) (levelCoconeIsColimit X m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ)

omit B in
/-- Every original chosen telescope stage leg is a closed embedding at every level. -/
theorem leg_level_isClosedEmbedding (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ) :
    IsClosedEmbedding (ConcreteCategory.hom
      (PointedCGWH.SequentialSpectrum.levelMap (leg X n) m).right) :=
  ClosedSequentialColimit.leg_isClosedEmbedding (levelCocone X m) (levelCoconeIsColimit X m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ) n

/-- The actual chosen TopCat colimit compares to the same original telescope level. -/
def telescopeTopLevelIso (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    colimit (levelDiagram X m ⋙ topFunctor) ≅
      topFunctor.obj (PointedCGWH.SequentialSpectrum.level (telescope X) m) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (levelCoconeTopIsColimit X m)

omit B in
/-- The whole forward comparison retains every original stage leg. -/
@[reassoc]
theorem telescopeTopLevelIso_hom_ι (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ) :
    colimit.ι (levelDiagram X m ⋙ topFunctor) n ≫ (telescopeTopLevelIso X m).hom =
      topFunctor.map (PointedCGWH.SequentialSpectrum.levelMap (leg X n) m) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (levelCoconeTopIsColimit X m) n

omit B in
/-- The whole inverse comparison retains every original stage leg. -/
@[reassoc]
theorem telescopeTopLevelIso_inv_ι (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ) :
    topFunctor.map (PointedCGWH.SequentialSpectrum.levelMap (leg X n) m) ≫
      (telescopeTopLevelIso X m).inv = colimit.ι (levelDiagram X m ⋙ topFunctor) n := by
  apply (cancel_mono (telescopeTopLevelIso X m).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (telescopeTopLevelIso_hom_ι X m n).symm

/-- The complete original level diagram functor retains every original spectrum map. -/
def levelDiagramFunctor (m : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ PointedCGWH.{u, v}) :=
  diagramFunctor ⋙ (Functor.whiskeringRight ℕ PointedCGWH.SequentialSpectrum.{u, v}
    PointedCGWH.{u, v}).obj (PointedCGWH.SequentialSpectrum.evaluation m)

/-- The entire original included level diagram retains its actual original maps. -/
def topLevelDiagramFunctor (m : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ TopCat.{v}) :=
  levelDiagramFunctor m ⋙ (Functor.whiskeringRight ℕ PointedCGWH.{u, v}
    TopCat.{v}).obj topFunctor

omit B in
/-- Every complete included original diagram-map component is unchanged. -/
theorem topLevelDiagramFunctor_map_app (m : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    ((topLevelDiagramFunctor m).map f).app n =
      topFunctor.map (PointedCGWH.SequentialSpectrum.levelMap ((stage n).functor.map f) m) :=
  rfl

omit B in
/-- The complete original chosen comparison is natural in every original spectrum map. -/
theorem telescopeTopLevelIso_naturality (m : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    colim.map ((topLevelDiagramFunctor m).map f) ≫ (telescopeTopLevelIso Y m).hom =
      (telescopeTopLevelIso X m).hom ≫
        topFunctor.map (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m) := by
  let E := PointedCGWH.SequentialSpectrum.evaluation.{u, v} m
  let U := topFunctor.{u, v}
  let α : levelDiagram X m ⋙ U ⟶ levelDiagram Y m ⋙ U :=
    Functor.whiskerRight (Functor.whiskerRight (diagramMap f) E) U
  change colim.map α ≫ (telescopeTopLevelIso Y m).hom =
    (telescopeTopLevelIso X m).hom ≫ U.map (E.map (telescopeFunctor.map f))
  apply telescope_colimitPointIso_naturality
    (U.mapCocone (levelCocone X m)) (U.mapCocone (levelCocone Y m))
    (levelCoconeTopIsColimit X m) (levelCoconeTopIsColimit Y m) α
  intro n
  have hE : E.map (leg X n) ≫ E.map (telescopeFunctor.map f) =
      E.map ((stage n).functor.map f) ≫ E.map (leg Y n) :=
    (E.map_comp _ _).symm.trans ((E.congr_map (leg_naturality f n)).trans (E.map_comp _ _))
  have hU : U.map (E.map (leg X n)) ≫ U.map (E.map (telescopeFunctor.map f)) =
      U.map (E.map ((stage n).functor.map f)) ≫ U.map (E.map (leg Y n)) :=
    (U.map_comp _ _).symm.trans ((U.congr_map hE).trans (U.map_comp _ _))
  exact hU

/-- The WHOLE chosen original telescope comparison includes all original input-map naturalities. -/
def telescopeTopEvaluationIso (m : ℕ) : topLevelDiagramFunctor.{u, v} m ⋙ colim ≅
    telescopeFunctor ⋙ PointedCGWH.SequentialSpectrum.evaluation m ⋙ topFunctor :=
  NatIso.ofComponents (fun X => telescopeTopLevelIso X m)
    (fun f => telescopeTopLevelIso_naturality m f)

omit B in
/-- The ENTIRE component-Iso function is the same original chosen comparison. -/
theorem telescopeTopEvaluationIso_app (m : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeTopEvaluationIso m).app X = telescopeTopLevelIso X m := rfl

omit B in
/-- Actual compact maps to the original telescope level factor beyond any original stage. -/
theorem compact_level_factor (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ)
    {K : Type w} [TopologicalSpace K] (hK : IsCompact (Set.univ : Set K))
    (f : C(K, topFunctor.obj (PointedCGWH.SequentialSpectrum.level (telescope X) m)))
    (n₀ : ℕ) : ∃ (n : ℕ), n₀ ≤ n ∧ ∃ (g : C(K,
      topFunctor.obj (PointedCGWH.SequentialSpectrum.level ((stage n).functor.obj X) m))),
      (topFunctor.map (PointedCGWH.SequentialSpectrum.levelMap (leg X n) m)).hom.comp g = f :=
  ClosedSequentialColimit.exists_later_stage_of_compact (levelCocone X m)
    (levelCoconeIsColimit X m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ) hK f n₀

omit B in
/-- Actual pointed compact maps retain the entire original point square and chosen factorization. -/
theorem pointed_compact_level_factor (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ)
    (K : PointedCGWH.{u, v}) (hK : IsCompact (Set.univ : Set (topFunctor.obj K)))
    (f : K ⟶ PointedCGWH.SequentialSpectrum.level (telescope X) m) :
    ∃ (n : ℕ) (g : K ⟶ PointedCGWH.SequentialSpectrum.level ((stage n).functor.obj X) m),
      g ≫ PointedCGWH.SequentialSpectrum.levelMap (leg X n) m = f :=
  ClosedSequentialColimit.exists_stage_of_pointed_compact (levelCocone X m)
    (levelCoconeIsColimit X m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ) K hK f

end PointedCGWH.SequentialSpectrum.MappingTelescope

namespace PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.ClosedSequentialColimit PointedCGWH.CubeColimitGeometry
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

omit B in
/-- Every original telescope-level cube factors through the SAME original pointed stage leg. -/
theorem cube_level_stage_factor (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ)
    (p : GenLoop (Fin n) (topFunctor.obj (PointedCGWH.SequentialSpectrum.level (telescope X) m))
      (underlyingBasepoint (PointedCGWH.SequentialSpectrum.level (telescope X) m))) (j₀ : ℕ) :
    ∃ (j : ℕ), j₀ ≤ j ∧ ∃ (q : GenLoop (Fin n)
      (topFunctor.obj (PointedCGWH.SequentialSpectrum.level ((stage j).functor.obj X) m))
      (underlyingBasepoint (PointedCGWH.SequentialSpectrum.level ((stage j).functor.obj X) m))),
      cubeMap n (PointedCGWH.SequentialSpectrum.levelMap (leg X j) m) q = p :=
  cube_stage_factor n (levelCocone X m) (levelCoconeIsColimit X m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ) p j₀

omit B in
/-- Actual original relative homotopies factor with both actual finite transition maps unchanged. -/
theorem relative_homotopy_level_stage_factor (X : PointedCGWH.SequentialSpectrum.{u, v})
    (m n i j : ℕ)
    (p : GenLoop (Fin n)
      (topFunctor.obj (PointedCGWH.SequentialSpectrum.level ((stage i).functor.obj X) m))
      (underlyingBasepoint (PointedCGWH.SequentialSpectrum.level ((stage i).functor.obj X) m)))
    (q : GenLoop (Fin n)
      (topFunctor.obj (PointedCGWH.SequentialSpectrum.level ((stage j).functor.obj X) m))
      (underlyingBasepoint (PointedCGWH.SequentialSpectrum.level ((stage j).functor.obj X) m)))
    (H : (cubeMap n (PointedCGWH.SequentialSpectrum.levelMap (leg X i) m) p).1.HomotopyRel
      (cubeMap n (PointedCGWH.SequentialSpectrum.levelMap (leg X j) m) q).1
      (Cube.boundary (Fin n))) :
    ∃ (k : ℕ) (hik : i ≤ k) (hjk : j ≤ k),
      ∃ (Hk : (cubeMap n ((levelDiagram X m).map (homOfLE hik)) p).1.HomotopyRel
        (cubeMap n ((levelDiagram X m).map (homOfLE hjk)) q).1 (Cube.boundary (Fin n))),
        (topFunctor.map (PointedCGWH.SequentialSpectrum.levelMap (leg X k) m)).hom.comp
          Hk.toHomotopy.toContinuousMap = H.toHomotopy.toContinuousMap :=
  relative_homotopy_stage_factor n (levelCocone X m) (levelCoconeIsColimit X m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ) i j p q H

end PointedCGWH.SequentialSpectrum.MappingTelescope
