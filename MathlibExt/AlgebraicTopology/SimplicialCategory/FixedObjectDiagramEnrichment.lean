/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomLaws
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# Actual fixed-object Hom diagrams as an enriched category

A genuine diagram of fixed-object enrichments gives an enrichment over
the pointwise monoidal category of scalar simplicial-set diagrams. Its
objects are the unchanged original labels, and all operations and laws
are the original operations at each indexing object.
-/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u} {J : Type v} [Category.{w} J]
  (F : J ⥤ FixedObjects O)

/-- The actual diagram of original Hom objects at two fixed individual labels. -/
def homDiagram (x y : O) : J ⥤ SSet.{u} := F ⋙ evaluation x y

/-- The actual original enriched identity in the pointwise Hom diagram. -/
def diagramIdentity (x : O) : 𝟙_ (J ⥤ SSet.{u}) ⟶ homDiagram F x x where
  app j := identityMap (F.obj j) x
  naturality j k f := by
    change 𝟙 _ ≫ identityMap (F.obj k) x = identityMap (F.obj j) x ≫ homMap (F.map f) x x
    exact (Category.id_comp _).trans (identityMap_homMap (F.map f) x).symm

/-- The actual original composition on the pointwise Hom diagrams. -/
def diagramComposition (x y z : O) : homDiagram F x y ⊗ homDiagram F y z ⟶ homDiagram F x z where
  app j := compositionMap (F.obj j) x y z
  naturality j k f := by
    change (homMap (F.map f) x y ⊗ₘ homMap (F.map f) y z) ≫
      compositionMap (F.obj k) x y z = compositionMap (F.obj j) x y z ≫ homMap (F.map f) x z
    exact (compositionMap_homMap (F.map f) x y z).symm

/-- The actual diagram enrichment, with every law derived at the original indexing objects. -/
@[instance_reducible]
def diagramEnrichment : EnrichedCategory (J ⥤ SSet.{u}) O where
  Hom := homDiagram F
  id := diagramIdentity F
  comp := diagramComposition F
  id_comp x y := by
    apply NatTrans.ext
    funext j
    change (λ_ (hom (F.obj j) x y)).inv ≫ identityMap (F.obj j) x ▷ _ ≫
      compositionMap (F.obj j) x x y = 𝟙 _
    exact e_id_comp SSet.{u} (vertex (F.obj j) x) (vertex (F.obj j) y)
  comp_id x y := by
    apply NatTrans.ext
    funext j
    change (ρ_ (hom (F.obj j) x y)).inv ≫ _ ◁ identityMap (F.obj j) y ≫
      compositionMap (F.obj j) x y y = 𝟙 _
    exact e_comp_id SSet.{u} (vertex (F.obj j) x) (vertex (F.obj j) y)
  assoc a b c d := by
    apply NatTrans.ext
    funext j
    change (α_ (hom (F.obj j) a b) (hom (F.obj j) b c) (hom (F.obj j) c d)).inv ≫
      compositionMap (F.obj j) a b c ▷ _ ≫ compositionMap (F.obj j) a c d =
        _ ◁ compositionMap (F.obj j) b c d ≫ compositionMap (F.obj j) a b d
    exact e_assoc SSet.{u} (vertex (F.obj j) a) (vertex (F.obj j) b)
      (vertex (F.obj j) c) (vertex (F.obj j) d)

/-- The pointwise enriched Hom is the same whole original Hom diagram. -/
theorem diagramEnrichment_hom (x y : O) : (diagramEnrichment F).Hom x y = homDiagram F x y := rfl

/-- Evaluation of the Hom diagram retains the original scalar Hom at that indexing object. -/
@[simp]
theorem homDiagram_obj (x y : O) (j : J) : (homDiagram F x y).obj j = hom (F.obj j) x y := rfl

/-- Every original diagram map acts by the same whole fixed-endpoint Hom map. -/
@[simp]
theorem homDiagram_map (x y : O) {j k : J} (f : j ⟶ k) :
    (homDiagram F x y).map f = homMap (F.map f) x y := rfl

end CategoryTheory.SimplicialEnrichment.FixedObjects
