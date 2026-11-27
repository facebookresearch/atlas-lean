/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectDiagramEnrichment
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomMaps
import Mathlib.CategoryTheory.Monoidal.Limits.Basic

/-!
# Actual limits of fixed-object simplicial enrichments

The scalar limit functor has its native lax monoidal structure. Transport
of the actual Hom-diagram enrichment therefore constructs the limit on
the same original object labels. Its whole enriched cone and universal
property retain every original Hom simplex, identity and composition.
-/

noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.HomLimit

variable {O : Type u} {J : Type v} [SmallCategory J] [HasLimitsOfShape J SSet.{u}]
  (F : J ⥤ FixedObjects O)

/-- The actual scalar limit enrichment on the same individually supplied original labels. -/
def object : FixedObjects O := by
  letI := diagramEnrichment F
  let X := TransportEnrichment (lim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) O
  exact ⟨SimplicialEnrichment.of X, rfl⟩

/-- The whole original limit Hom is the actual scalar limit of those same Hom objects. -/
theorem object_hom (x y : O) : hom (object F) x y = limit (homDiagram F x y) := rfl

/-- The native lax monoidal unit gives the actual original limit identity. -/
theorem object_identity (x : O) : identityMap (object F) x =
    Functor.LaxMonoidal.ε (lim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) ≫ lim.map (diagramIdentity F x) := rfl

/-- The native limit tensorator gives actual composition at the same three original labels. -/
theorem object_composition (x y z : O) : compositionMap (object F) x y z =
    Functor.LaxMonoidal.μ (lim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) (homDiagram F x y) (homDiagram F y z) ≫
      lim.map (diagramComposition F x y z) := rfl

/-- The actual scalar Hom projection at the supplied indexing object. -/
def projectionHom (j : J) (x y : O) : hom (object F) x y ⟶ hom (F.obj j) x y :=
  limit.π (homDiagram F x y) j

private theorem projection_identity (j : J) (x : O) :
    identityMap (object F) x ≫ projectionHom F j x x = identityMap (F.obj j) x := by
  change (Functor.LaxMonoidal.ε (lim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) ≫
    limMap (diagramIdentity F x)) ≫ limit.π (homDiagram F x x) j = _
  rw [Category.assoc, limMap_π, ← Category.assoc, lim_ε_π, Category.id_comp]
  rfl

private theorem projection_composition (j : J) (x y z : O) :
    compositionMap (object F) x y z ≫ projectionHom F j x z =
      (projectionHom F j x y ⊗ₘ projectionHom F j y z) ≫ compositionMap (F.obj j) x y z := by
  change (Functor.LaxMonoidal.μ (lim : (J ⥤ SSet.{u}) ⥤ SSet.{u})
    (homDiagram F x y) (homDiagram F y z) ≫ limMap (diagramComposition F x y z)) ≫
      limit.π (homDiagram F x z) j = _
  rw [Category.assoc, limMap_π, ← Category.assoc, lim_μ_π]
  rfl

/-- The genuine whole enriched limit projection fixes every individual original label. -/
def projection (j : J) : object F ⟶ F.obj j :=
  ofHomMaps (projectionHom F j) (projection_identity F j) (projection_composition F j)

/-- The whole original Hom map of the limit projection is its literal scalar limit leg. -/
theorem homMap_projection (j : J) (x y : O) :
    homMap (projection F j) x y = limit.π (homDiagram F x y) j := homMap_ofHomMaps _ _ _ x y

/-- The actual original fixed-object limit cone. -/
def cone : Cone F where
  pt := object F
  π := {
    app := projection F
    naturality j k f := by
      apply homMaps_ext
      intro x y
      change homMap (𝟙 (object F) ≫ projection F k) x y = homMap (projection F j ≫ F.map f) x y
      rw [homMap_comp, homMap_id, Category.id_comp, homMap_projection,
        homMap_comp, homMap_projection]
      exact (limit.w (homDiagram F x y) f).symm }

/-- Evaluate the supplied whole original cone at the same two individual labels. -/
abbrev homCone (s : Cone F) (x y : O) : Cone (homDiagram F x y) := (evaluation x y).mapCone s

/-- The actual scalar universal Hom map from the supplied original cone. -/
def homLift (s : Cone F) (x y : O) : hom s.pt x y ⟶ hom (object F) x y :=
  limit.lift (homDiagram F x y) (homCone F s x y)

private theorem homLift_identity (s : Cone F) (x : O) :
    identityMap s.pt x ≫ homLift F s x x = identityMap (object F) x := by
  apply (limit.isLimit (homDiagram F x x)).hom_ext
  intro j
  change (identityMap s.pt x ≫ homLift F s x x) ≫ projectionHom F j x x =
    identityMap (object F) x ≫ projectionHom F j x x
  have h : homLift F s x x ≫ projectionHom F j x x = homMap (s.π.app j) x x :=
    limit.lift_π (homCone F s x x) j
  rw [projection_identity, Category.assoc, h]
  exact identityMap_homMap (s.π.app j) x

private theorem homLift_composition (s : Cone F) (x y z : O) :
    compositionMap s.pt x y z ≫ homLift F s x z =
      (homLift F s x y ⊗ₘ homLift F s y z) ≫ compositionMap (object F) x y z := by
  apply (limit.isLimit (homDiagram F x z)).hom_ext
  intro j
  change (compositionMap s.pt x y z ≫ homLift F s x z) ≫ projectionHom F j x z =
    ((homLift F s x y ⊗ₘ homLift F s y z) ≫ compositionMap (object F) x y z) ≫ projectionHom F j x z
  have hxy : homLift F s x y ≫ projectionHom F j x y = homMap (s.π.app j) x y :=
    limit.lift_π (homCone F s x y) j
  have hyz : homLift F s y z ≫ projectionHom F j y z = homMap (s.π.app j) y z :=
    limit.lift_π (homCone F s y z) j
  have hxz : homLift F s x z ≫ projectionHom F j x z = homMap (s.π.app j) x z :=
    limit.lift_π (homCone F s x z) j
  calc
    _ = compositionMap s.pt x y z ≫ homMap (s.π.app j) x z := by rw [Category.assoc, hxz]
    _ = (homMap (s.π.app j) x y ⊗ₘ homMap (s.π.app j) y z) ≫ compositionMap (F.obj j) x y z :=
      compositionMap_homMap (s.π.app j) x y z
    _ = ((homLift F s x y ≫ projectionHom F j x y) ⊗ₘ
      (homLift F s y z ≫ projectionHom F j y z)) ≫ compositionMap (F.obj j) x y z :=
        by rw [hxy, hyz]
    _ = (homLift F s x y ⊗ₘ homLift F s y z) ≫
      (projectionHom F j x y ⊗ₘ projectionHom F j y z) ≫ compositionMap (F.obj j) x y z :=
        (congrArg (fun t => t ≫ compositionMap (F.obj j) x y z)
          (tensorHom_comp_tensorHom (homLift F s x y) (homLift F s y z)
            (projectionHom F j x y) (projectionHom F j y z)).symm).trans (Category.assoc _ _ _)
    _ = _ := by rw [Category.assoc, projection_composition]

/-- The genuine whole enriched universal cone map preserves all original identities and
composition. -/
def lift (s : Cone F) : s.pt ⟶ object F := ofHomMaps (homLift F s) (homLift_identity F s)
  (homLift_composition F s)

/-- The universal enriched map has the same whole scalar Hom lift. -/
theorem homMap_lift (s : Cone F) (x y : O) : homMap (lift F s) x y = homLift F s x y :=
  homMap_ofHomMaps _ _ _ x y

/-- Every original whole cone leg is read back exactly by the limit universal map. -/
theorem lift_projection (s : Cone F) (j : J) : lift F s ≫ projection F j = s.π.app j := by
  apply homMaps_ext
  intro x y
  rw [homMap_comp, homMap_lift, homMap_projection]
  exact limit.lift_π (homCone F s x y) j

/-- The actual fixed-object enriched cone has the full original limit universal property. -/
def isLimit : IsLimit (cone F) where
  lift := lift F
  fac := lift_projection F
  uniq s m h := by
    change s.pt ⟶ object F at m
    change ∀ j, m ≫ projection F j = s.π.app j at h
    apply homMaps_ext
    intro x y
    rw [homMap_lift]
    apply (limit.isLimit (homDiagram F x y)).hom_ext
    intro j
    change homMap m x y ≫ homMap (projection F j) x y =
      homLift F s x y ≫ homMap (projection F j) x y
    rw [← homMap_comp, h j, homMap_projection]
    exact (limit.lift_π (homCone F s x y) j).symm

end CategoryTheory.SimplicialEnrichment.FixedObjects.HomLimit

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u} {J : Type v} [SmallCategory J] [HasLimitsOfShape J SSet.{u}]

/-- Actual scalar limits supply all limits of this small shape in the original fixed-object
enrichment category. -/
instance hasLimitsOfShape : HasLimitsOfShape J (FixedObjects O) where
  has_limit F := ⟨⟨HomLimit.cone F, HomLimit.isLimit F⟩⟩

end CategoryTheory.SimplicialEnrichment.FixedObjects
