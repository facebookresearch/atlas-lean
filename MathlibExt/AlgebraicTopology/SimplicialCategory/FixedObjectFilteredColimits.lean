/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFilteredColimitCocone

/-!
# Genuine filtered colimits of fixed-object simplicial enrichments

The actual scalar colimit Hom maps assemble the universal enriched map.
The whole fixed-object cocone is proved colimiting, and every original
Hom evaluation preserves that colimit. The proof uses actual monoidal
scalar colimits, original enriched-map laws and full Hom extensionality.
-/

noncomputable section
universe u v w
open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FilteredColimit

variable {O : Type u} {J : Type v} [Category.{w} J] [IsFiltered J] [Small.{u} J]
  (F : J ⥤ FixedObjects O)

/-- Evaluate an actual original fixed-object cocone on the same two individual endpoint labels. -/
abbrev homCocone (s : Cocone F) (x y : O) : Cocone (homDiagram F x y) :=
  (evaluation x y).mapCocone s

/-- The actual scalar universal map from the whole filtered Hom colimit. -/
def homDesc (s : Cocone F) (x y : O) : hom (object F) x y ⟶ hom s.pt x y :=
  colimit.desc (homDiagram F x y) (homCocone F s x y)

/-- The universal Hom map retains the exact whole original cocone leg at every indexing object. -/
theorem homDesc_fac (s : Cocone F) (j : J) (x y : O) :
    colimit.ι (homDiagram F x y) j ≫ homDesc F s x y = homMap (s.ι.app j) x y :=
  colimit.ι_desc (homCocone F s x y) j

set_option backward.isDefEq.respectTransparency.types false in
private theorem homDesc_identity (s : Cocone F) (x : O) :
    identityMap (object F) x ≫ homDesc F s x x = identityMap s.pt x := by
  let j : J := Classical.choice IsFiltered.nonempty
  have h := identityMap_homMap (injection F j) x
  have hf : homMap (injection F j) x x ≫ homDesc F s x x = homMap (s.ι.app j) x x := by
    rw [homMap_injection]
    change colimit.ι (homDiagram F x x) j ≫ homDesc F s x x = homMap (s.ι.app j) x x
    exact homDesc_fac F s j x x
  exact (congrArg (fun k => k ≫ homDesc F s x x) h.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => identityMap (F.obj j) x ≫ k) hf).trans
        (identityMap_homMap (s.ι.app j) x)))

set_option backward.isDefEq.respectTransparency.types false in
private theorem homDesc_composition (s : Cocone F) (x y z : O) :
    compositionMap (object F) x y z ≫ homDesc F s x z =
      (homDesc F s x y ⊗ₘ homDesc F s y z) ≫ compositionMap s.pt x y z := by
  let μ := Functor.Monoidal.μIso (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u})
    (homDiagram F x y) (homDiagram F y z)
  apply (cancel_epi μ.inv).1
  apply (colimit.isColimit (homDiagram F x y ⊗ homDiagram F y z)).hom_ext
  intro j
  let iX := homMap (injection F j) x y
  let iY := homMap (injection F j) y z
  let iZ := homMap (injection F j) x z
  have ht : (iX ⊗ₘ iY) ≫ μ.hom = colimit.ι (homDiagram F x y ⊗ homDiagram F y z) j := by
    dsimp only [iX, iY]
    rw [homMap_injection, homMap_injection]
    change (colimit.ι (homDiagram F x y) j ⊗ₘ colimit.ι (homDiagram F y z) j) ≫
      Functor.LaxMonoidal.μ (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u})
        (homDiagram F x y) (homDiagram F y z) = colimit.ι (homDiagram F x y ⊗ homDiagram F y z) j
    exact SSet.FilteredColimit.injection_tensor J j (homDiagram F x y) (homDiagram F y z)
  have hι : colimit.ι (homDiagram F x y ⊗ homDiagram F y z) j ≫ μ.inv = iX ⊗ₘ iY := by
    have h := congrArg (fun k => k ≫ μ.inv) ht.symm
    exact h.trans ((Category.assoc _ _ _).trans
      ((congrArg (fun k => (iX ⊗ₘ iY) ≫ k) μ.hom_inv_id).trans (Category.comp_id _)))
  have hx : iX ≫ homDesc F s x y = homMap (s.ι.app j) x y := by
    dsimp only [iX]
    rw [homMap_injection]
    change colimit.ι (homDiagram F x y) j ≫ homDesc F s x y = homMap (s.ι.app j) x y
    exact homDesc_fac F s j x y
  have hy : iY ≫ homDesc F s y z = homMap (s.ι.app j) y z := by
    dsimp only [iY]
    rw [homMap_injection]
    change colimit.ι (homDiagram F y z) j ≫ homDesc F s y z = homMap (s.ι.app j) y z
    exact homDesc_fac F s j y z
  have hz : iZ ≫ homDesc F s x z = homMap (s.ι.app j) x z := by
    dsimp only [iZ]
    rw [homMap_injection]
    change colimit.ι (homDiagram F x z) j ≫ homDesc F s x z = homMap (s.ι.app j) x z
    exact homDesc_fac F s j x z
  have hp : (iX ⊗ₘ iY) ≫ compositionMap (object F) x y z ≫ homDesc F s x z =
      (iX ⊗ₘ iY) ≫ (homDesc F s x y ⊗ₘ homDesc F s y z) ≫ compositionMap s.pt x y z := by
    calc
      _ = (compositionMap (F.obj j) x y z ≫ iZ) ≫ homDesc F s x z :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ homDesc F s x z)
            (compositionMap_homMap (injection F j) x y z).symm)
      _ = compositionMap (F.obj j) x y z ≫ homMap (s.ι.app j) x z :=
        (Category.assoc _ _ _).trans (congrArg (fun k => compositionMap (F.obj j) x y z ≫ k) hz)
      _ = (homMap (s.ι.app j) x y ⊗ₘ homMap (s.ι.app j) y z) ≫ compositionMap s.pt x y z :=
        compositionMap_homMap (s.ι.app j) x y z
      _ = ((iX ≫ homDesc F s x y) ⊗ₘ (iY ≫ homDesc F s y z)) ≫ compositionMap s.pt x y z :=
        congrArg (fun k => k ≫ compositionMap s.pt x y z) (congrArg₂ (fun a b => a ⊗ₘ b) hx hy).symm
      _ = _ := (congrArg (fun k => k ≫ compositionMap s.pt x y z)
        (tensorHom_comp_tensorHom iX iY (homDesc F s x y) (homDesc F s y z)).symm).trans
          (Category.assoc _ _ _)
  have hLeft := congrArg (fun k => k ≫ compositionMap (object F) x y z ≫ homDesc F s x z) hι
  have hRight := congrArg (fun k => k ≫
    (homDesc F s x y ⊗ₘ homDesc F s y z) ≫ compositionMap s.pt x y z) hι
  change colimit.ι (homDiagram F x y ⊗ homDiagram F y z) j ≫
      (μ.inv ≫ compositionMap (object F) x y z ≫ homDesc F s x z) =
    colimit.ι (homDiagram F x y ⊗ homDiagram F y z) j ≫
      (μ.inv ≫ (homDesc F s x y ⊗ₘ homDesc F s y z) ≫ compositionMap s.pt x y z)
  exact (Category.assoc _ _ _).symm.trans
    ((hLeft.trans (hp.trans hRight.symm)).trans (Category.assoc _ _ _))

/-- The genuine whole enriched universal map, with the same original object labels. -/
def desc (s : Cocone F) : object F ⟶ s.pt :=
  ofHomMaps (homDesc F s) (homDesc_identity F s) (homDesc_composition F s)

/-- Its whole original Hom map is exactly the actual scalar colimit universal map. -/
@[simp]
theorem homMap_desc (s : Cocone F) (x y : O) : homMap (desc F s) x y = homDesc F s x y :=
  homMap_ofHomMaps _ _ _ x y

/-- The universal map factors every whole original cocone leg. -/
theorem desc_fac (s : Cocone F) (j : J) : injection F j ≫ desc F s = s.ι.app j := by
  apply homMaps_ext
  intro x y
  rw [homMap_comp, homMap_injection, homMap_desc]
  exact homDesc_fac F s j x y

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual enriched universal map is unique on all original Hom simplices and object labels. -/
theorem desc_uniq (s : Cocone F) (d : object F ⟶ s.pt)
    (hd : ∀ j, injection F j ≫ d = s.ι.app j) : d = desc F s := by
  apply homMaps_ext
  intro x y
  rw [homMap_desc]
  apply (colimit.isColimit (homDiagram F x y)).hom_ext
  intro j
  change colimit.ι (homDiagram F x y) j ≫ homMap d x y =
    colimit.ι (homDiagram F x y) j ≫ homDesc F s x y
  have h := congrArg (fun f : F.obj j ⟶ s.pt => homMap f x y) (hd j)
  rw [homMap_comp, homMap_injection] at h
  change colimit.ι (homDiagram F x y) j ≫ homMap d x y = homMap (s.ι.app j) x y at h
  exact h.trans (homDesc_fac F s j x y).symm

/-- The actual fixed-object filtered cocone has the complete enriched colimit universal property. -/
def isColimit : IsColimit (cocone F) where
  desc := desc F
  fac := desc_fac F
  uniq := desc_uniq F

/-- Fixed-object simplicial enrichments have these genuine small filtered colimits. -/
instance hasColimitsOfShape : HasColimitsOfShape J (FixedObjects O) where
  has_colimit F := HasColimit.mk ⟨cocone F, isColimit F⟩

/-- Evaluating the canonical cocone gives the genuine scalar Hom colimit. -/
def evaluatedIsColimit (x y : O) : IsColimit ((evaluation x y).mapCocone (cocone F)) := by
  apply IsColimit.ofIsoColimit (colimit.isColimit (homDiagram F x y))
  refine Cocone.ext (Iso.refl _) ?_
  intro j
  change colimit.ι (homDiagram F x y) j ≫ 𝟙 _ = homMap (injection F j) x y
  exact (Category.comp_id _).trans (homMap_injection F j x y).symm

/-- Every whole original Hom evaluation preserves the actual enriched filtered colimit. -/
instance evaluationPreservesColimit (x y : O) : PreservesColimit F (evaluation x y) :=
  preservesColimit_of_preserves_colimit_cocone (isColimit F) (evaluatedIsColimit F x y)

/-- Hom evaluation preserves all genuine small filtered colimits of this indexing shape. -/
instance evaluationPreservesColimitsOfShape (x y : O) : PreservesColimitsOfShape J (evaluation x y) where
  preservesColimit {K} := evaluationPreservesColimit K x y

end CategoryTheory.SimplicialEnrichment.FixedObjects.FilteredColimit
