/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.DiagonalHomotopy

/-!
# FULL original Type and positive-group structure squares on the SAME colimits

The whole original cube and group sigma transformations act on each
actual original MC and R-iteration diagram. Their maps retain EVERY
original finite-index and input-spectrum naturality. Original projection
squares commute with the SAME original structure maps. The genuine Type
and Group colimit universal properties on every original telescope leg
prove the FULL structure squares of both original comparisons. Both
directions of the original telescope/R colimit comparisons are retained.
No structure-square law, alternative diagram, source Cof or stable-model
dictionary is an input. Diagonal tail/index identification and arbitrary
input Omega/forward8.8 remain distinct later obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v uC vC uJ vJ
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace CategoryTheory.Limits
variable {C : Type uC} [Category.{vC} C] {J : Type uJ} [Category.{vJ} J]
  [HasColimitsOfShape J C]

/-- The actual chosen full colimit-point comparisons preserve every complete cocone-map square. -/
private theorem nativeStructure_colimitPointIso_naturality {F G : J ⥤ C} (c : Cocone F) (d :
  Cocone G)
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

namespace GrpCat.FilteredColimits

/-- The actual whole filtered group-colimit map preserves every full competing-cocone square. -/
private theorem nativeStructure_desc_map_naturality {F G : ℕ ⥤ GrpCat.{v}} (c : Cocone F) (d :
  Cocone G)
    (a : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ j : ℕ, c.ι.app j ≫ g = a.app j ≫ d.ι.app j) :
    colimitMap a ≫ (GrpCat.FilteredColimits.colimitCoconeIsColimit G).desc d =
      (GrpCat.FilteredColimits.colimitCoconeIsColimit F).desc c ≫ g := by
  apply (GrpCat.FilteredColimits.colimitCoconeIsColimit F).hom_ext
  intro j
  have hF := (GrpCat.FilteredColimits.colimitCoconeIsColimit F).fac c j
  have hG := (GrpCat.FilteredColimits.colimitCoconeIsColimit G).fac d j
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun r => r ≫ (GrpCat.FilteredColimits.colimitCoconeIsColimit G).desc d)
      (colimitMap_ι a j)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun r => a.app j ≫ r) hG).trans
            ((hg j).symm.trans
              ((congrArg (fun r => r ≫ g) hF.symm).trans (Category.assoc _ _ _))))))

end GrpCat.FilteredColimits

private theorem originalStructureInverseSquare
    {C : Type uC} [Category.{vC} C] {A B D E : C}
    (e : A ≅ D) (f : B ≅ E) (a : A ⟶ B) (b : D ⟶ E)
    (h : a ≫ f.hom = e.hom ≫ b) : b ≫ f.inv = e.inv ≫ a := by
  apply (cancel_mono f.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, h,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem originalStructureComparisonSquare
    {C : Type uC} [Category.{vC} C] {A B D E F G : C}
    (e : A ≅ D) (f : B ≅ E) (p : A ⟶ F) (q : B ⟶ G)
    (a : A ⟶ B) (b : D ⟶ E) (c : F ⟶ G)
    (h₁ : a ≫ f.hom = e.hom ≫ b) (h₂ : a ≫ q = p ≫ c) :
    b ≫ (f.inv ≫ q) = (e.inv ≫ p) ≫ c := by
  have h := originalStructureInverseSquare e f a b h₁
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun r => r ≫ q) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun r => e.inv ≫ r) h₂).trans (Category.assoc _ _ _).symm)))

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.HomotopyStructureColimitGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop (iterationDiagram iterate)
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
open PointedCGWH.SequentialHomotopyColimit
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The entire actual original cube sigma acts on every full original spectrum diagram. -/
def cubeStructureDiagram (D : ℕ ⥤ PointedCGWH.SequentialSpectrum.{u, v}) (m k : ℕ) :
    D ⋙ PointedCGWH.SequentialSpectrum.evaluation m ⋙ piNFunctor k ⟶
      D ⋙ PointedCGWH.SequentialSpectrum.evaluation (m + 1) ⋙ piNFunctor (k + 1) :=
  Functor.whiskerLeft D (cubeStructureNatTrans m k)

/-- The entire actual original group sigma acts on every full original spectrum diagram. -/
def groupStructureDiagram (D : ℕ ⥤ PointedCGWH.SequentialSpectrum.{u, v}) (m k : ℕ) :
    D ⋙ PointedCGWH.SequentialSpectrum.evaluation m ⋙ piNPositiveFunctor k ⟶
      D ⋙ PointedCGWH.SequentialSpectrum.evaluation (m + 1) ⋙ piNPositiveFunctor (k + 1) :=
  Functor.whiskerLeft D (groupStructureNatTrans m k)

/-- The WHOLE MC Type diagram structure keeps every original stage and original input map. -/
def stageTypeStructureNatTrans (m k : ℕ) : typeHomotopyDiagramFunctor.{u, v} m k ⟶
    typeHomotopyDiagramFunctor (m + 1) (k + 1) where
  app X := cubeStructureDiagram (diagram X) m k
  naturality _ _ f := by
    apply NatTrans.ext
    funext n
    exact (cubeStructureNatTrans m k).naturality ((stage n).functor.map f)

/-- The WHOLE MC group diagram structure keeps every original stage and original input map. -/
def stageGroupStructureNatTrans (m k : ℕ) : groupHomotopyDiagramFunctor.{u, v} m k ⟶
    groupHomotopyDiagramFunctor (m + 1) (k + 1) where
  app X := groupStructureDiagram (diagram X) m k
  naturality _ _ f := by
    apply NatTrans.ext
    funext n
    exact (groupStructureNatTrans m k).naturality ((stage n).functor.map f)

/-- The WHOLE original R Type structure retains the SAME complete original iterate maps. -/
def iterationTypeStructureNatTrans (m k : ℕ) : typeIterationDiagramFunctor.{u, v} m k ⟶
    typeIterationDiagramFunctor (m + 1) (k + 1) where
  app X := cubeStructureDiagram (iterationDiagram X) m k
  naturality _ _ f := by
    apply NatTrans.ext
    funext n
    exact (cubeStructureNatTrans m k).naturality ((iterate n).map f)

/-- The WHOLE original R group structure retains the SAME complete original iterate maps. -/
def iterationGroupStructureNatTrans (m k : ℕ) : groupIterationDiagramFunctor.{u, v} m k ⟶
    groupIterationDiagramFunctor (m + 1) (k + 1) where
  app X := groupStructureDiagram (iterationDiagram X) m k
  naturality _ _ f := by
    apply NatTrans.ext
    funext n
    exact (groupStructureNatTrans m k).naturality ((iterate n).map f)

/-- Every ENTIRE MC Type structure component is the literal original stage sigma function. -/
theorem stageTypeStructureNatTrans_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((stageTypeStructureNatTrans m k).app X).app n =
      (cubeStructureNatTrans m k).app ((stage n).functor.obj X) := rfl

/-- Every ENTIRE MC group structure component is the literal original stage sigma map. -/
theorem stageGroupStructureNatTrans_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((stageGroupStructureNatTrans m k).app X).app n =
      (groupStructureNatTrans m k).app ((stage n).functor.obj X) := rfl

/-- Every ENTIRE R Type structure component is the SAME original iterate sigma function. -/
theorem iterationTypeStructureNatTrans_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((iterationTypeStructureNatTrans m k).app X).app n =
      (cubeStructureNatTrans m k).app ((iterate n).obj X) := rfl

/-- Every ENTIRE R group structure component is the SAME original iterate sigma map. -/
theorem iterationGroupStructureNatTrans_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((iterationGroupStructureNatTrans m k).app X).app n =
      (groupStructureNatTrans m k).app ((iterate n).obj X) := rfl

/-- ALL full original Type projections commute with the original MC and R sigma maps. -/
theorem projectionType_structure_whole (m k : ℕ) :
    stageTypeStructureNatTrans.{u, v} m k ≫ typeDiagramProjectionNatTrans (m + 1) (k + 1) =
      typeDiagramProjectionNatTrans m k ≫ iterationTypeStructureNatTrans m k := by
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext n
  exact ((cubeStructureNatTrans m k).naturality ((projection n).app X)).symm

/-- ALL full original group projections commute with the original MC and R sigma maps. -/
theorem projectionGroup_structure_whole (m k : ℕ) :
    stageGroupStructureNatTrans.{u, v} m k ≫ groupDiagramProjectionNatTrans (m + 1) (k + 1) =
      groupDiagramProjectionNatTrans m k ≫ iterationGroupStructureNatTrans m k := by
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext n
  exact ((groupStructureNatTrans m k).naturality ((projection n).app X)).symm

/-- The entire original MC Type colimit structure is the actual chosen Type colimit map. -/
def stageTypeColimitStructureNatTrans (m k : ℕ) : typeHomotopyDiagramFunctor.{u, v} m k ⋙
    colim ⟶ typeHomotopyDiagramFunctor (m + 1) (k + 1) ⋙ colim :=
  Functor.whiskerRight (stageTypeStructureNatTrans m k)
    (colim : (ℕ ⥤ Type v) ⥤ Type v)

/-- The entire original MC group colimit structure uses the SAME genuine filtered quotient. -/
def stageGroupColimitStructureNatTrans (m k : ℕ) : groupHomotopyDiagramFunctor.{u, v} m k ⋙
    GrpCat.FilteredColimits.colimitFunctor ⟶
      groupHomotopyDiagramFunctor (m + 1) (k + 1) ⋙
        GrpCat.FilteredColimits.colimitFunctor :=
  Functor.whiskerRight (stageGroupStructureNatTrans m k)
    GrpCat.FilteredColimits.colimitFunctor

/-- The entire original R Type colimit structure keeps every original iterate map. -/
def iterationTypeColimitStructureNatTrans (m k : ℕ) : typeIterationDiagramFunctor.{u, v} m k ⋙
    colim ⟶ typeIterationDiagramFunctor (m + 1) (k + 1) ⋙ colim :=
  Functor.whiskerRight (iterationTypeStructureNatTrans m k)
    (colim : (ℕ ⥤ Type v) ⥤ Type v)

/-- The entire original R group colimit structure uses the SAME genuine group colimit functor. -/
def iterationGroupColimitStructureNatTrans (m k : ℕ) :
    groupIterationDiagramFunctor.{u, v} m k ⋙ GrpCat.FilteredColimits.colimitFunctor ⟶
      groupIterationDiagramFunctor (m + 1) (k + 1) ⋙
        GrpCat.FilteredColimits.colimitFunctor :=
  Functor.whiskerRight (iterationGroupStructureNatTrans m k)
    GrpCat.FilteredColimits.colimitFunctor

/-- ALL original Type colimit projections retain the full original structure square. -/
theorem projectionTypeColimit_structure_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    colim.map ((stageTypeStructureNatTrans m k).app X) ≫
        colim.map ((typeDiagramProjectionNatTrans (m + 1) (k + 1)).app X) =
      colim.map ((typeDiagramProjectionNatTrans m k).app X) ≫
        colim.map ((iterationTypeStructureNatTrans m k).app X) := by
  have h := congr_app (projectionType_structure_whole m k) X
  exact (colim.map_comp _ _).symm.trans ((colim.congr_map h).trans (colim.map_comp _ _))

/-- ALL original group colimit projections retain the full original structure square. -/
theorem projectionGroupColimit_structure_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    GrpCat.FilteredColimits.colimitMap ((stageGroupStructureNatTrans m k).app X) ≫
        GrpCat.FilteredColimits.colimitMap
          ((groupDiagramProjectionNatTrans (m + 1) (k + 1)).app X) =
      GrpCat.FilteredColimits.colimitMap ((groupDiagramProjectionNatTrans m k).app X) ≫
        GrpCat.FilteredColimits.colimitMap ((iterationGroupStructureNatTrans m k).app X) := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} :=
    GrpCat.FilteredColimits.colimitFunctor
  have h := congr_app (projectionGroup_structure_whole m k) X
  exact (Q.map_comp _ _).symm.trans ((Q.congr_map h).trans (Q.map_comp _ _))

/-- Genuine original Type UPL and EVERY original leg prove the complete Type structure square. -/
theorem telescopeTypeHomotopy_structure_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    colim.map ((stageTypeStructureNatTrans m k).app X) ≫
        (telescopeTypeHomotopyIso X (m + 1) (k + 1)).hom =
      (telescopeTypeHomotopyIso X m k).hom ≫ (cubeStructureNatTrans m k).app (telescope X) := by
  let c := (piNFunctor k).mapCocone (levelCocone X m)
  let d := (piNFunctor (k + 1)).mapCocone (levelCocone X (m + 1))
  let a : levelDiagram X m ⋙ piNFunctor k ⟶ levelDiagram X (m + 1) ⋙ piNFunctor (k + 1) :=
    (stageTypeStructureNatTrans m k).app X
  exact nativeStructure_colimitPointIso_naturality c d
    (piNIsColimit k (levelCocone X m) (levelCoconeIsColimit X m)
      (fun _ _ f => levelDiagram_map_isClosedEmbedding X m f))
    (piNIsColimit (k + 1) (levelCocone X (m + 1)) (levelCoconeIsColimit X (m + 1))
      (fun _ _ f => levelDiagram_map_isClosedEmbedding X (m + 1) f))
    a ((cubeStructureNatTrans m k).app (telescope X))
    (fun n => (cubeStructureNatTrans m k).naturality (leg X n))

/-- Genuine original Group UPL and EVERY original leg prove the complete group structure square. -/
theorem telescopeGroupHomotopy_structure_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    GrpCat.FilteredColimits.colimitMap ((stageGroupStructureNatTrans m k).app X) ≫
        (telescopeGroupHomotopyIso X (m + 1) (k + 1)).hom =
      (telescopeGroupHomotopyIso X m k).hom ≫ (groupStructureNatTrans m k).app (telescope X) := by
  let F := levelDiagram X m ⋙ piNPositiveFunctor k
  let G := levelDiagram X (m + 1) ⋙ piNPositiveFunctor (k + 1)
  let c := (piNPositiveFunctor k).mapCocone (levelCocone X m)
  let d := (piNPositiveFunctor (k + 1)).mapCocone (levelCocone X (m + 1))
  let a : F ⟶ G := (stageGroupStructureNatTrans m k).app X
  have hF : (telescopeGroupHomotopyIso X m k).hom =
      (GrpCat.FilteredColimits.colimitCoconeIsColimit F).desc c :=
    piNPositiveComparisonIso_hom k (levelCocone X m) (levelCoconeIsColimit X m)
      (fun _ _ f => levelDiagram_map_isClosedEmbedding X m f)
  have hG : (telescopeGroupHomotopyIso X (m + 1) (k + 1)).hom =
      (GrpCat.FilteredColimits.colimitCoconeIsColimit G).desc d :=
    piNPositiveComparisonIso_hom (k + 1) (levelCocone X (m + 1))
      (levelCoconeIsColimit X (m + 1))
      (fun _ _ f => levelDiagram_map_isClosedEmbedding X (m + 1) f)
  have h := GrpCat.FilteredColimits.nativeStructure_desc_map_naturality c d a
    ((groupStructureNatTrans m k).app (telescope X))
    (fun n => (groupStructureNatTrans m k).naturality (leg X n))
  exact (congrArg (fun f => GrpCat.FilteredColimits.colimitMap a ≫ f) hG).trans
    (h.trans (congrArg (fun f => f ≫ (groupStructureNatTrans m k).app (telescope X)) hF.symm))

/-- The WHOLE actual original Type telescope comparison preserves EVERY structure component. -/
theorem telescopeTypeHomotopy_structure_whole (m k : ℕ) :
    stageTypeColimitStructureNatTrans.{u, v} m k ≫
        (telescopeTypeHomotopyEvaluationIso (m + 1) (k + 1)).hom =
      (telescopeTypeHomotopyEvaluationIso m k).hom ≫
        Functor.whiskerLeft telescopeFunctor (cubeStructureNatTrans m k) := by
  apply NatTrans.ext
  funext X
  exact telescopeTypeHomotopy_structure_hom m k X

/-- The WHOLE actual original group telescope comparison preserves EVERY structure component. -/
theorem telescopeGroupHomotopy_structure_whole (m k : ℕ) :
    stageGroupColimitStructureNatTrans.{u, v} m k ≫
        (telescopeGroupHomotopyEvaluationIso (m + 1) (k + 1)).hom =
      (telescopeGroupHomotopyEvaluationIso m k).hom ≫
        Functor.whiskerLeft telescopeFunctor (groupStructureNatTrans m k) := by
  apply NatTrans.ext
  funext X
  exact telescopeGroupHomotopy_structure_hom m k X

/-- The ENTIRE original inverse Type comparison preserves the same full structure square. -/
theorem telescopeTypeHomotopy_structure_inv_whole (m k : ℕ) :
    Functor.whiskerLeft telescopeFunctor (cubeStructureNatTrans m k) ≫
        (telescopeTypeHomotopyEvaluationIso (m + 1) (k + 1)).inv =
      (telescopeTypeHomotopyEvaluationIso m k).inv ≫
        stageTypeColimitStructureNatTrans.{u, v} m k :=
  originalStructureInverseSquare (telescopeTypeHomotopyEvaluationIso m k)
    (telescopeTypeHomotopyEvaluationIso (m + 1) (k + 1))
    (stageTypeColimitStructureNatTrans m k)
    (Functor.whiskerLeft telescopeFunctor (cubeStructureNatTrans m k))
    (telescopeTypeHomotopy_structure_whole m k)

/-- The ENTIRE original inverse group comparison preserves the same full structure square. -/
theorem telescopeGroupHomotopy_structure_inv_whole (m k : ℕ) :
    Functor.whiskerLeft telescopeFunctor (groupStructureNatTrans m k) ≫
        (telescopeGroupHomotopyEvaluationIso (m + 1) (k + 1)).inv =
      (telescopeGroupHomotopyEvaluationIso m k).inv ≫
        stageGroupColimitStructureNatTrans.{u, v} m k :=
  originalStructureInverseSquare (telescopeGroupHomotopyEvaluationIso m k)
    (telescopeGroupHomotopyEvaluationIso (m + 1) (k + 1))
    (stageGroupColimitStructureNatTrans m k)
    (Functor.whiskerLeft telescopeFunctor (groupStructureNatTrans m k))
    (telescopeGroupHomotopy_structure_whole m k)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- Every ENTIRE original Type telescope/R comparison retains its full structure-map square. -/
theorem telescopeTypeIteration_structure_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (cubeStructureNatTrans m k).app (telescope X) ≫
        (telescopeTypeIterationColimitNatIso (m + 1) (k + 1)).hom.app X =
      (telescopeTypeIterationColimitNatIso m k).hom.app X ≫
        colim.map ((iterationTypeStructureNatTrans m k).app X) := by
  have h := originalStructureComparisonSquare (telescopeTypeHomotopyIso X m k)
    (telescopeTypeHomotopyIso X (m + 1) (k + 1))
    (colim.map ((typeDiagramProjectionNatTrans m k).app X))
    (colim.map ((typeDiagramProjectionNatTrans (m + 1) (k + 1)).app X))
    (colim.map ((stageTypeStructureNatTrans m k).app X))
    ((cubeStructureNatTrans m k).app (telescope X))
    (colim.map ((iterationTypeStructureNatTrans m k).app X))
    (telescopeTypeHomotopy_structure_hom m k X)
    (projectionTypeColimit_structure_hom m k X)
  exact (congrArg (fun f => (cubeStructureNatTrans m k).app (telescope X) ≫ f)
      (telescopeTypeIterationColimitNatIso_hom_app (m + 1) (k + 1) X)).trans
    (h.trans (congrArg (fun f => f ≫
      colim.map ((iterationTypeStructureNatTrans m k).app X))
        (telescopeTypeIterationColimitNatIso_hom_app m k X).symm))

/-- Every ENTIRE original group telescope/R comparison retains its full structure-map square. -/
theorem telescopeGroupIteration_structure_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (groupStructureNatTrans m k).app (telescope X) ≫
        (telescopeGroupIterationColimitNatIso (m + 1) (k + 1)).hom.app X =
      (telescopeGroupIterationColimitNatIso m k).hom.app X ≫
        GrpCat.FilteredColimits.colimitMap ((iterationGroupStructureNatTrans m k).app X) := by
  have h := originalStructureComparisonSquare (telescopeGroupHomotopyIso X m k)
    (telescopeGroupHomotopyIso X (m + 1) (k + 1))
    (GrpCat.FilteredColimits.colimitMap ((groupDiagramProjectionNatTrans m k).app X))
    (GrpCat.FilteredColimits.colimitMap
      ((groupDiagramProjectionNatTrans (m + 1) (k + 1)).app X))
    (GrpCat.FilteredColimits.colimitMap ((stageGroupStructureNatTrans m k).app X))
    ((groupStructureNatTrans m k).app (telescope X))
    (GrpCat.FilteredColimits.colimitMap ((iterationGroupStructureNatTrans m k).app X))
    (telescopeGroupHomotopy_structure_hom m k X)
    (projectionGroupColimit_structure_hom m k X)
  exact (congrArg (fun f => (groupStructureNatTrans m k).app (telescope X) ≫ f)
      (telescopeGroupIterationColimitNatIso_hom_app (m + 1) (k + 1) X)).trans
    (h.trans (congrArg (fun f => f ≫
      GrpCat.FilteredColimits.colimitMap ((iterationGroupStructureNatTrans m k).app X))
        (telescopeGroupIterationColimitNatIso_hom_app m k X).symm))

/-- The WHOLE Type telescope/R NatIso retains every actual original structure-map component. -/
theorem telescopeTypeIteration_structure_whole (m k : ℕ) :
    Functor.whiskerLeft telescopeFunctor (cubeStructureNatTrans m k) ≫
        (telescopeTypeIterationColimitNatIso (m + 1) (k + 1)).hom =
      (telescopeTypeIterationColimitNatIso m k).hom ≫
        iterationTypeColimitStructureNatTrans.{u, v} m k := by
  apply NatTrans.ext
  funext X
  exact telescopeTypeIteration_structure_hom m k X

/-- The WHOLE group telescope/R NatIso retains every actual original structure-map component. -/
theorem telescopeGroupIteration_structure_whole (m k : ℕ) :
    Functor.whiskerLeft telescopeFunctor (groupStructureNatTrans m k) ≫
        (telescopeGroupIterationColimitNatIso (m + 1) (k + 1)).hom =
      (telescopeGroupIterationColimitNatIso m k).hom ≫
        iterationGroupColimitStructureNatTrans.{u, v} m k := by
  apply NatTrans.ext
  funext X
  exact telescopeGroupIteration_structure_hom m k X

/-- The ENTIRE inverse Type telescope/R comparison retains every original structure square. -/
theorem telescopeTypeIteration_structure_inv_whole (m k : ℕ) :
    iterationTypeColimitStructureNatTrans.{u, v} m k ≫
        (telescopeTypeIterationColimitNatIso (m + 1) (k + 1)).inv =
      (telescopeTypeIterationColimitNatIso m k).inv ≫
        Functor.whiskerLeft telescopeFunctor (cubeStructureNatTrans m k) :=
  originalStructureInverseSquare (telescopeTypeIterationColimitNatIso m k)
    (telescopeTypeIterationColimitNatIso (m + 1) (k + 1))
    (Functor.whiskerLeft telescopeFunctor (cubeStructureNatTrans m k))
    (iterationTypeColimitStructureNatTrans m k) (telescopeTypeIteration_structure_whole m k)

/-- The ENTIRE inverse group telescope/R comparison retains every original structure square. -/
theorem telescopeGroupIteration_structure_inv_whole (m k : ℕ) :
    iterationGroupColimitStructureNatTrans.{u, v} m k ≫
        (telescopeGroupIterationColimitNatIso (m + 1) (k + 1)).inv =
      (telescopeGroupIterationColimitNatIso m k).inv ≫
        Functor.whiskerLeft telescopeFunctor (groupStructureNatTrans m k) :=
  originalStructureInverseSquare (telescopeGroupIterationColimitNatIso m k)
    (telescopeGroupIterationColimitNatIso (m + 1) (k + 1))
    (Functor.whiskerLeft telescopeFunctor (groupStructureNatTrans m k))
    (iterationGroupColimitStructureNatTrans m k) (telescopeGroupIteration_structure_whole m k)

end PointedCGWH.SequentialSpectrum.MappingTelescope.HomotopyStructureColimitGeometry
