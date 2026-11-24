/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeAttachmentScalarFreePresentation
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordPushout

/-!
# Full scalar free presentations of actual monic free-quiver pushouts

The original attaching data are read from genuine monic quiver maps and
the actual whole enriched attaching functor. The normalized word pushout
is compared with the supplied actual pushout by its proved universal
property. Its full scalar free presentation transfers through that same
enriched isomorphism, retaining every old and new coefficient map.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeQuiverMonoPushout
open RelativeAttachment RelativeWords

variable {O : Type u} {Q R : SimplicialQuiver.Data O} {C D : FixedObjects O}
  (m : ∀ x y : O, Q.Hom x y ⟶ R.Hom x y)
  (hm : ∀ x y, Mono (m x y)) (s : FreeQuiver.object Q ⟶ C)

/-- Read the actual original monic attaching data, including the original whole attaching maps. -/
def data : Data C where
  domain := Q
  target := R
  inclusion := m
  mono := hm
  attaching x y := FreeQuiver.generator Q x y ≫ homMap s x y

/-- The actual domain leg is exactly the supplied whole original enriched attaching functor. -/
theorem data_domainMap : domainMap (data m hm s) = s := by
  apply FreeQuiver.generators_ext Q
  intro x y
  exact FreeQuiver.generator_extend Q C _ x y

/-- The actual target leg is exactly the whole original free map. -/
theorem data_targetMap : targetMap (data m hm s) = FreeQuiver.map m := rfl

variable (j : C ⟶ D) (k : FreeQuiver.object R ⟶ D)
  (hp : IsPushout s (FreeQuiver.map m) j k)

/-- The normalized original word object is the SAME actual enriched pushout. -/
def comparison : object (data m hm s) ≅ D :=
  (isPushout (data m hm s)).isoIsPushout _ _ (by
    rw [data_domainMap, data_targetMap]
    exact hp)

/-- The comparison retains the exact whole original old pushout leg. -/
theorem oldMap_comparison : oldMap (data m hm s) ≫ (comparison m hm s j k hp).hom = j :=
  (isPushout (data m hm s)).inl_isoIsPushout_hom _ _ (by
    rw [data_domainMap, data_targetMap]
    exact hp)

/-- The comparison retains the exact whole original free-target pushout leg. -/
theorem newMap_comparison : newMap (data m hm s) ≫ (comparison m hm s j k hp).hom = k :=
  (isPushout (data m hm s)).inr_isoIsPushout_hom _ _ (by
    rw [data_domainMap, data_targetMap]
    exact hp)

/-- Transfer the constructed full scalar presentation through the actual original enriched isomorphism. -/
def scalarPresentation (q : SimplexCategoryᵒᵖ)
    (P : FreePresentation.{u,u,u} (scalarCategory C q)) :
    FreePresentation.{u,u,u} (scalarCategory D q) where
  quiver := (scalarFreePresentation (data m hm s) q P).quiver
  map {a b} p := (homMap (comparison m hm s j k hp).hom a b).app q
    ((scalarFreePresentation (data m hm s) q P).map p)
  map_id a := by
    rw [(scalarFreePresentation (data m hm s) q P).map_id]
    exact congr($(identityMap_homMap (comparison m hm s j k hp).hom a).app q PUnit.unit)
  map_comp {a b c} p r := by
    rw [(scalarFreePresentation (data m hm s) q P).map_comp]
    exact congr($(compositionMap_homMap (comparison m hm s j k hp).hom a b c).app q
      ((scalarFreePresentation (data m hm s) q P).map p,
        (scalarFreePresentation (data m hm s) q P).map r))
  bijective a b := by
    let e := (evaluation a b).mapIso (comparison m hm s j k hp)
    let eQ := ((CategoryTheory.evaluation _ _).obj q).mapIso e
    have he : Function.Bijective ((homMap (comparison m hm s j k hp).hom a b).app q) :=
      (ConcreteCategory.bijective_of_isIso eQ.hom)
    exact he.comp ((scalarFreePresentation (data m hm s) q P).bijective a b)

/-- Every original old generating path retains the supplied original pushout coefficient map. -/
theorem scalarPresentation_oldPath (q : SimplexCategoryᵒᵖ)
    (P : FreePresentation.{u,u,u} (scalarCategory C q)) {x y : O}
    (p : @Quiver.Path O P.quiver x y) :
    (scalarPresentation m hm s j k hp q P).map
        (FreePaths.oldPath P.quiver (newAt (data m hm s) q) p) =
      (homMap j x y).app q (P.map p) := by
  change (homMap (comparison m hm s j k hp).hom x y).app q
    ((scalarFreePresentation (data m hm s) q P).map _) = _
  rw [scalarFreePresentation_oldPath]
  have h := congrArg (fun F => (homMap F x y).app q (P.map p))
    (oldMap_comparison m hm s j k hp)
  rw [homMap_comp, homMap_oldMap] at h
  exact h

/-- The extended free presentation uses exactly the old generators and the actual target complement. -/
theorem scalarPresentation_quiver (q : SimplexCategoryᵒᵖ)
    (P : FreePresentation.{u,u,u} (scalarCategory C q)) :
    (scalarPresentation m hm s j k hp q P).quiver =
      FreePaths.sumQuiver P.quiver (newAt (data m hm s) q) := rfl

/-- Every complete new coefficient is read by the SAME original free-target pushout map. -/
theorem scalarPresentation_new (q : SimplexCategoryᵒᵖ)
    (P : FreePresentation.{u,u,u} (scalarCategory C q)) {x y : O}
    (g : newAt (data m hm s) q x y) :
    (scalarPresentation m hm s j k hp q P).map
        (@Quiver.Hom.toPath O (FreePaths.sumQuiver P.quiver (newAt (data m hm s) q))
          x y (Sum.inr g)) =
      (FreeQuiver.generator R x y ≫ homMap k x y).app q g.val := by
  change (homMap (comparison m hm s j k hp).hom x y).app q
    ((scalarFreePresentation (data m hm s) q P).map _) = _
  rw [scalarFreePresentation_new]
  have h := congrArg (fun F => FreeQuiver.generator R x y ≫ homMap F x y)
    (newMap_comparison m hm s j k hp)
  have hcomp := homMap_comp (newMap (data m hm s)) (comparison m hm s j k hp).hom x y
  have h' := (congrArg (fun f => FreeQuiver.generator R x y ≫ f) hcomp).symm.trans h
  change FreeQuiver.generator R x y ≫
    (homMap (FreeQuiver.extend R (object (data m hm s)) (newHom (data m hm s))) x y ≫
      homMap (comparison m hm s j k hp).hom x y) =
    FreeQuiver.generator R x y ≫ homMap k x y at h'
  have hgen := FreeQuiver.generator_extend (data m hm s).target
    (object (data m hm s)) (newHom (data m hm s)) x y
  have h'' := (congrArg (fun f => f ≫ homMap (comparison m hm s j k hp).hom x y) hgen).symm.trans
    (((Category.assoc _ _ _).symm).trans h')
  exact congrArg (fun f => f.app q g.val) h''

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeQuiverMonoPushout
