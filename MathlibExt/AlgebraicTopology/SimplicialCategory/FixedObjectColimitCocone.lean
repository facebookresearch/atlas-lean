/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectPresentations
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectDiagramGenerators

/-!
# The actual arbitrary fixed-object presentation cocone

The three original relation families enforce stage identities, stage
composition and actual diagram maps. They construct the whole enriched
cocone on the unchanged object labels, with exact generator readback.
No colimit or enriched-model conclusion is supplied as an input.
-/

noncomputable section
universe u v w
open CategoryTheory Limits MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.DiagramPresentation
open SimplicialQuiver

variable {O : Type u} {J : Type v} [Category.{w} J] [Small.{u} J]
  (F : J ⥤ FixedObjects O)

/-- The actual presentation of the original diagram on its same individual object labels. -/
abbrev object : FixedObjects O := Presentations.object (quiver F) (relations F)

/-- The same original stage Hom injection into the actual presented enrichment. -/
def injectionHom (j : J) (x y : O) : hom (F.obj j) x y ⟶ hom (object F) x y :=
  stageHom F j x y ≫ Presentations.generator (quiver F) (relations F) x y

private theorem injection_identity (j : J) (x : O) :
    identityMap (F.obj j) x ≫ injectionHom F j x x = identityMap (object F) x := by
  ext q a
  cases a
  exact Presentations.relation_eq (quiver F) (relations F) q x x _ _
    (Relation.identity j q x)

private theorem injection_composition (j : J) (x y z : O) :
    compositionMap (F.obj j) x y z ≫ injectionHom F j x z =
      (injectionHom F j x y ⊗ₘ injectionHom F j y z) ≫ compositionMap (object F) x y z := by
  ext q a
  rcases a with ⟨a, b⟩
  exact Presentations.relation_eq (quiver F) (relations F) q x z _ _
    (Relation.composition j q x y z a b)

/-- The actual whole enriched cocone leg, derived from the original unit and composition
relations. -/
def injection (j : J) : F.obj j ⟶ object F :=
  ofHomMaps (injectionHom F j) (injection_identity F j) (injection_composition F j)

/-- Each cocone leg is the same whole original stage Hom injection. -/
@[simp]
theorem homMap_injection (j : J) (x y : O) :
    homMap (injection F j) x y = injectionHom F j x y := homMap_ofHomMaps _ _ _ x y

/-- Each cocone leg retains the same supplied individual original object label. -/
@[simp]
theorem injection_obj (j : J) (a : (F.obj j).val) :
    (injection F j).val.obj a = vertex (object F) (label (F.obj j) a) := rfl

private theorem injection_naturality {j k : J} (f : j ⟶ k) (x y : O) :
    homMap (F.map f) x y ≫ injectionHom F k x y = injectionHom F j x y := by
  ext q a
  exact (Presentations.relation_eq (quiver F) (relations F) q x y _ _
    (Relation.diagram f q x y a)).symm

/-- The genuine fixed-object cocone over the original arbitrary small diagram. -/
def cocone : Cocone F where
  pt := object F
  ι := {
    app := injection F
    naturality j k f := by
      change F.map f ≫ injection F k = injection F j ≫ 𝟙 (object F)
      apply homMaps_ext
      intro x y
      rw [homMap_comp, homMap_comp, homMap_id, Category.comp_id,
        homMap_injection, homMap_injection]
      exact injection_naturality F f x y }

end CategoryTheory.SimplicialEnrichment.FixedObjects.DiagramPresentation
