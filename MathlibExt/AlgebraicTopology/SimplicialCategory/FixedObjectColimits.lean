/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectColimitCocone
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectColimitInterpretation

/-!
# Genuine arbitrary small colimits of fixed-object simplicial enrichments

The presentation of the actual stage Homs and diagram equations has
the full enriched colimit universal property. The original object labels
are unchanged, including empty diagrams; only the actual generating Hom
paths are identified by the proved relation families.
-/

noncomputable section
universe u v w
open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.DiagramPresentation

variable {O : Type u} {J : Type v} [Category.{w} J] [Small.{u} J]
  (F : J ⥤ FixedObjects O)

/-- The actual enriched universal map, interpreting every original stage Hom by the supplied
cocone. -/
def desc (s : Cocone F) : object F ⟶ s.pt :=
  Presentations.extend (quiver F) (relations F) s.pt (interpretation F s).map
    (interpretation_relations F s)

/-- Each original generator is read back by its same actual cocone interpretation. -/
theorem generator_desc (s : Cocone F) (x y : O) :
    Presentations.generator (quiver F) (relations F) x y ≫ homMap (desc F s) x y =
      (interpretation F s).map x y :=
  Presentations.generator_extend (quiver F) (relations F) s.pt
    (interpretation F s).map (interpretation_relations F s) x y

/-- The universal map retains each same individual original object label. -/
@[simp]
theorem desc_obj (s : Cocone F) (a : O) : (desc F s).val.obj a = vertex s.pt a := rfl

/-- The universal enriched map factors every whole original cocone leg. -/
theorem desc_fac (s : Cocone F) (j : J) : injection F j ≫ desc F s = s.ι.app j := by
  apply homMaps_ext
  intro x y
  rw [homMap_comp, homMap_injection]
  change (stageHom F j x y ≫ Presentations.generator (quiver F) (relations F) x y) ≫
    homMap (desc F s) x y = homMap (s.ι.app j) x y
  rw [Category.assoc, generator_desc]
  exact stage_interpretation F s j x y

/-- Whole original colimit maps are unique on all actual stage Homs and fixed object labels. -/
theorem desc_uniq (s : Cocone F) (d : object F ⟶ s.pt)
    (hd : ∀ j, injection F j ≫ d = s.ι.app j) : d = desc F s := by
  apply Presentations.generators_ext (quiver F) (relations F)
  intro x y
  apply Sigma.hom_ext
  intro j
  change stageHom F j x y ≫
      (Presentations.generator (quiver F) (relations F) x y ≫ homMap d x y) =
    stageHom F j x y ≫
      (Presentations.generator (quiver F) (relations F) x y ≫ homMap (desc F s) x y)
  have h := congrArg (fun f : F.obj j ⟶ s.pt => homMap f x y) (hd j)
  have hf := congrArg (fun f : F.obj j ⟶ s.pt => homMap f x y) (desc_fac F s j)
  rw [homMap_comp, homMap_injection] at h hf
  exact (Category.assoc _ _ _).symm.trans ((h.trans hf.symm).trans (Category.assoc _ _ _))

/-- The actual presentation cocone satisfies the entire enriched colimit universal property. -/
def isColimit : IsColimit (cocone F) where
  desc := desc F
  fac := desc_fac F
  uniq := desc_uniq F

/-- Fixed-object simplicial enrichments have these actual arbitrary small colimits. -/
instance hasColimitsOfShape : HasColimitsOfShape J (FixedObjects O) where
  has_colimit F := HasColimit.mk ⟨cocone F, isColimit F⟩

end CategoryTheory.SimplicialEnrichment.FixedObjects.DiagramPresentation
