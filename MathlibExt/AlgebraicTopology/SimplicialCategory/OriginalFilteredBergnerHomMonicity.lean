/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFilteredUnderSourceCocone
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnderHomColimitReadback
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnderHomSourceUnit
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerCofibrationHomMonicity
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictIsoHom
import MathlibExt.AlgebraicTopology.SimplicialSet.FilteredColimitStageData

/-!
# The same full original Hom maps into filtered C0 colimits are monic

The actual original under-source tail has its genuine colimit. Every
original transition Hom is monic by C0 lifting, and only the two true
under-triangle endpoint equalities act on that full map. The canonical
simplicial filtered-colimit theorem and the same source-unit triangle
prove monicity of the original enriched cocone Hom, without weakening
or replacing that map.
-/

noncomputable section
universe u
open CategoryTheory Limits
attribute [local instance] IsFiltered.isConnected

namespace CategoryTheory.SimplicialEnrichment.OriginalUnderHom

/-- Original C0 lifting makes the same full under-Hom coefficient monic, retaining its two true endpoints. -/
theorem map_mono_of_cofibration (C : Carrier.{u}) (x y : C)
    {A B : Under C} (f : A ⟶ B) (hf : Bergner.cofibrations f.right) :
    Mono (map C x y f) := by
  let _ := Bergner.cofibration_original_hom_mono f.right hf (A.hom.obj x) (A.hom.obj y)
  change Mono (f.right.map (A.hom.obj x) (A.hom.obj y) ≫
    eqToHom (congrArg₂ (fun a b : B.right => a ⟶[SSet.{u}] b)
      (endpoint C f x) (endpoint C f y)))
  infer_instance

end CategoryTheory.SimplicialEnrichment.OriginalUnderHom

namespace CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom

/-- Every same complete original cocone Hom map in a genuine filtered C0 diagram is monic. -/
theorem cocone_hom_mono {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ Carrier.{u}) (s : Cocone F) (hs : IsColimit s)
    (hC : ∀ {i j : J} (f : i ⟶ j), Bergner.cofibrations (F.map f))
    (j : J) (x y : F.obj j) : Mono ((s.ι.app j).map x y) := by
  let U := sourceDiagram F j
  let c := sourceCocone F s j
  let H := U ⋙ OriginalUnderHom.functor (F.obj j) x y
  have hc : IsColimit ((OriginalUnderHom.functor (F.obj j) x y).mapCocone c) :=
    OriginalUnderHomColimit.originalIsColimit U c (sourceIsColimit F s j hs) x y
      (fun h => Bergner.cofibration_objects_injective _ (hC h.right))
  have hH : ∀ {a b : Under j} (g : a ⟶ b), Mono (H.map g) :=
    fun g => OriginalUnderHom.map_mono_of_cofibration (F.obj j) x y (U.map g) (hC g.right)
  let a : Under j := Under.mk (𝟙 j)
  let _ : Mono (((OriginalUnderHom.functor (F.obj j) x y).mapCocone c).ι.app a) :=
    SSet.FilteredColimitStage.cocone_legs_mono_of_maps_mono _ hc (fun {_ _} g => hH g) a
  let _ : IsIso (U.obj a).hom := by
    change IsIso (F.map (𝟙 j))
    infer_instance
  let _ : IsIso ((OriginalUnderHom.sourceUnit U x y).app a) :=
    (isoHomIso (asIso ((U.obj a).hom)) x y).isIso_hom
  have hm : Mono ((OriginalUnderHom.sourceUnit U x y).app a ≫
      ((OriginalUnderHom.functor (F.obj j) x y).mapCocone c).ι.app a) := inferInstance
  exact (OriginalUnderHom.sourceUnit_cocone U x y c a) ▸ hm

end CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom
