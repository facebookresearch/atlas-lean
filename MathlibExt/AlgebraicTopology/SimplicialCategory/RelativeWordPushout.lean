/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordSpan
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordExtensionality
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# The genuine original enriched pushout represented by normalized relative words

Every actual enriched cocone on the original free attaching span extends
by complete normalized-word evaluation. Both whole legs factor, and
actual word extensionality proves uniqueness. Thus the constructed word
enrichment is the genuine pushout, retaining original objects, loop pairs,
identities and arbitrary composites without a pushout outcome as an input.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment

variable {O : Type u} {C D : FixedObjects O}

/-- Read the same original target-generator maps from the actual target-free enriched leg. -/
def coconeHom (T : Data C) (K : FreeQuiver.object T.target ⟶ D) (x y : O) :
    T.target.Hom x y ⟶ hom D x y := FreeQuiver.generator T.target x y ≫ homMap K x y

/-- The entire actual enriched cocone condition gives its same original attaching-Hom square. -/
theorem cocone_compat (T : Data C) (F : C ⟶ D) (K : FreeQuiver.object T.target ⟶ D)
    (h : domainMap T ≫ F = targetMap T ≫ K) (x y : O) :
    T.inclusion x y ≫ coconeHom T K x y = T.attaching x y ≫ homMap F x y := by
  have hh := congrArg (fun f : FreeQuiver.object T.domain ⟶ D =>
    FreeQuiver.generator T.domain x y ≫ homMap f x y) h
  rw [homMap_comp, homMap_comp] at hh
  change FreeQuiver.generator T.domain x y ≫
      (homMap (FreeQuiver.extend T.domain C T.attaching) x y ≫ homMap F x y) =
    FreeQuiver.generator T.domain x y ≫ (homMap (FreeQuiver.map T.inclusion) x y ≫ homMap K x y) at hh
  rw [← Category.assoc, FreeQuiver.generator_extend, ← Category.assoc,
    FreeQuiver.generator_map, Category.assoc] at hh
  exact hh.symm

/-- The actual whole normalized-word extension of an original enriched pushout cocone. -/
def pushoutDesc (T : Data C) (F : C ⟶ D) (K : FreeQuiver.object T.target ⟶ D)
    (h : domainMap T ≫ F = targetMap T ≫ K) : object T ⟶ D :=
  desc T F (coconeHom T K) (cocone_compat T F K h)

/-- The actual whole original-enrichment leg factors through the same constructed pushout map. -/
theorem pushoutDesc_left (T : Data C) (F : C ⟶ D) (K : FreeQuiver.object T.target ⟶ D)
    (h : domainMap T ≫ F = targetMap T ≫ K) : oldMap T ≫ pushoutDesc T F K h = F :=
  oldMap_desc T F (coconeHom T K) (cocone_compat T F K h)

/-- The actual whole target-free leg factors through the same constructed pushout map. -/
theorem pushoutDesc_right (T : Data C) (F : C ⟶ D) (K : FreeQuiver.object T.target ⟶ D)
    (h : domainMap T ≫ F = targetMap T ≫ K) : newMap T ≫ pushoutDesc T F K h = K := by
  apply FreeQuiver.generators_ext T.target
  intro x y
  rw [homMap_comp]
  change FreeQuiver.generator T.target x y ≫
      (homMap (FreeQuiver.extend T.target (object T) (newHom T)) x y ≫
        homMap (desc T F (coconeHom T K) (cocone_compat T F K h)) x y) =
    FreeQuiver.generator T.target x y ≫ homMap K x y
  rw [← Category.assoc, FreeQuiver.generator_extend, newHom_desc]
  rfl

/-- The actual whole enriched extension of an original pushout cocone is unique on all original words and objects. -/
theorem pushoutDesc_unique (T : Data C) (F : C ⟶ D) (K : FreeQuiver.object T.target ⟶ D)
    (h : domainMap T ≫ F = targetMap T ≫ K) (H : object T ⟶ D)
    (hOld : oldMap T ≫ H = F) (hNew : newMap T ≫ H = K) : H = pushoutDesc T F K h := by
  apply desc_unique T F (coconeHom T K) (cocone_compat T F K h) H hOld
  intro x y
  have hh := congrArg (fun f : FreeQuiver.object T.target ⟶ D =>
    FreeQuiver.generator T.target x y ≫ homMap f x y) hNew
  rw [homMap_comp] at hh
  change FreeQuiver.generator T.target x y ≫
      (homMap (FreeQuiver.extend T.target (object T) (newHom T)) x y ≫ homMap H x y) =
    FreeQuiver.generator T.target x y ≫ homMap K x y at hh
  rw [← Category.assoc, FreeQuiver.generator_extend] at hh
  exact hh

/-- The actual original free attaching span has this whole normalized-word cocone. -/
def pushoutCocone (T : Data C) : PushoutCocone (domainMap T) (targetMap T) :=
  PushoutCocone.mk (oldMap T) (newMap T) (domainMap_oldMap T)

/-- The actual normalized-word cocone satisfies the complete original enriched pushout universal property. -/
def pushoutIsColimit (T : Data C) : IsColimit (pushoutCocone T) :=
  PushoutCocone.IsColimit.mk (domainMap_oldMap T)
    (fun s => pushoutDesc T s.inl s.inr s.condition)
    (fun s => pushoutDesc_left T s.inl s.inr s.condition)
    (fun s => pushoutDesc_right T s.inl s.inr s.condition)
    (fun s H hOld hNew => pushoutDesc_unique T s.inl s.inr s.condition H hOld hNew)

/-- The original attaching square is genuinely a pushout in the actual fixed-object enriched category. -/
theorem isPushout (T : Data C) : IsPushout (domainMap T) (targetMap T) (oldMap T) (newMap T) :=
  IsPushout.of_isColimit (pushoutIsColimit T)

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
