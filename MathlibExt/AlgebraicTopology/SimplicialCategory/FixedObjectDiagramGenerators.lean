/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomLaws
import MathlibExt.AlgebraicTopology.SimplicialCategory.Presentation
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Actual generators and relations of a fixed-object diagram

The generating Hom objects are coproducts of the original stage Homs.
The three relation families impose the actual stage identity, stage
composition and original diagram maps. All original labels, scalar
degrees and loop pairs are retained; no colimit outcome is an input.
-/

noncomputable section
universe u v w uC
open CategoryTheory Limits MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.DiagramPresentation
open SimplicialQuiver

variable {O : Type u} {J : Type v} [Category.{w} J] [Small.{u} J]
  (F : J ⥤ FixedObjects O)

/-- Coproducts of all original stage Hom objects at the same supplied individual labels. -/
def quiver : Data O where
  Hom x y := ∐ fun j : J => hom (F.obj j) x y

/-- The actual coproduct injection of an original stage Hom object. -/
def stageHom (j : J) (x y : O) : hom (F.obj j) x y ⟶ (quiver F).Hom x y :=
  Sigma.ι (fun k : J => hom (F.obj k) x y) j

/-- The same original stage Hom map, followed by the actual length-one free generator. -/
def freeStageHom (j : J) (x y : O) : hom (F.obj j) x y ⟶ freeHom (quiver F) x y :=
  stageHom F j x y ≫ generator (quiver F) x y

/-- Every original stage generator is a real length-one path in its scalar degree. -/
theorem stage_generator_length (j : J) (q : SimplexCategoryᵒᵖ) (x y : O)
    (a : (hom (F.obj j) x y).obj q) :
    pathLength (quiver F) q ((freeStageHom F j x y).app q a) = 1 :=
  SimplicialQuiver.generator_length (quiver F) q x y ((stageHom F j x y).app q a)

/-- The actual diagram relations on original whole free paths. -/
inductive Relation : ∀ (q : SimplexCategoryᵒᵖ) (x y : O),
    Path (quiver F) q x y → Path (quiver F) q x y → Prop
  | identity (j : J) (q : SimplexCategoryᵒᵖ) (x : O) :
      Relation q x x
        ((freeStageHom F j x x).app q ((identityMap (F.obj j) x).app q PUnit.unit))
        (@Quiver.Path.nil O (quiverAt (quiver F) q) x)
  | composition (j : J) (q : SimplexCategoryᵒᵖ) (x y z : O)
      (a : (hom (F.obj j) x y).obj q) (b : (hom (F.obj j) y z).obj q) :
      Relation q x z
        ((freeStageHom F j x z).app q ((compositionMap (F.obj j) x y z).app q (a, b)))
        (@Quiver.Path.comp O (quiverAt (quiver F) q) x y z
          ((freeStageHom F j x y).app q a) ((freeStageHom F j y z).app q b))
  | diagram {j k : J} (f : j ⟶ k) (q : SimplexCategoryᵒᵖ) (x y : O)
      (a : (hom (F.obj j) x y).obj q) :
      Relation q x y ((freeStageHom F j x y).app q a)
        ((freeStageHom F k x y).app q ((homMap (F.map f) x y).app q a))

/-- The supplied actual diagram equations as the existing presentation relation family. -/
abbrev relations : Relations (quiver F) := Relation F

/-- The original generator evaluation through any actual interpretation of the coproduct Homs. -/
theorem stage_eval {C : Type uC} [EnrichedCategory SSet.{u} C]
    (I : Interpretation (quiver F) C) (j : J) (q : SimplexCategoryᵒᵖ) (x y : O)
    (a : (hom (F.obj j) x y).obj q) :
    I.evalPath q ((freeStageHom F j x y).app q a) =
      (stageHom F j x y ≫ I.map x y).app q a := by
  have h := congrArg (fun f => stageHom F j x y ≫ f) (I.generator_eval x y)
  exact congrArg (fun f => f.app q a) h

end CategoryTheory.SimplicialEnrichment.FixedObjects.DiagramPresentation
