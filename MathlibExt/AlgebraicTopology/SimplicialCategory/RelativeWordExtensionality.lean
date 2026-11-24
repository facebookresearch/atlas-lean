/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordDesc

/-!
# Whole original extensionality of maps from the normalized word enrichment

Every actual enriched map is determined by its original enrichment leg
and its entire target-generator maps. The proof retains each original
word and uses its actual decomposition and the enriched composition map.
Consequently the constructed compatible extension is genuinely unique.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} {C D : FixedObjects O}

/-- Read the actual scalar map of a whole enriched map on an individual normalized original word. -/
abbrev mapAt (T : Data C) (H : object T ⟶ D) (q : SimplexCategoryᵒᵖ)
    {x y : O} (p : WordAt T q x y) : (hom D x y).obj q := (homMap H x y).app q p

/-- Every actual enriched map preserves whole normalized-word composition. -/
theorem mapAt_comp (T : Data C) (H : object T ⟶ D) (q : SimplexCategoryᵒᵖ)
    {x y z : O} (p : WordAt T q x y) (t : WordAt T q y z) :
    mapAt T H q (compWords T q p t) =
      (compositionMap D x y z).app q (mapAt T H q p, mapAt T H q t) :=
  congr($(compositionMap_homMap H x y z).app q (p, t))

/-- Every actual enriched map reads the complete original segment, new letter and remaining word by target
  composition. -/
theorem mapAt_cons (T : Data C) (H : object T ⟶ D) (q : SimplexCategoryᵒᵖ)
    {a x y b : O} (h : (hom C a x).obj q) (g : newAt T q x y) (p : WordAt T q y b) :
    mapAt T H q (consWord T q h g p) =
      (compositionMap D a x b).app q (mapAt T H q (oldWord T q h),
        (compositionMap D x y b).app q
          (mapAt T H q (@generator O (scalarCategory C q) (newAt T q) x y g), mapAt T H q p)) := by
  have hc : consWord T q h g p = compWords T q (oldWord T q h)
      (compWords T q (@generator O (scalarCategory C q) (newAt T q) x y g) p) :=
    (@cons_eq_comp O (scalarCategory C q) (newAt T q) a x y b h g p).trans
      (@Word.assoc O (scalarCategory C q) (newAt T q) a x y b _ _ _)
  rw [hc, mapAt_comp, mapAt_comp]

/-- The actual original leg equation determines the same whole scalar old-word map. -/
theorem mapAt_old (T : Data C) (F : C ⟶ D) (H : object T ⟶ D) (hH : oldMap T ≫ H = F)
    (q : SimplexCategoryᵒᵖ) {x y : O} (p : (hom C x y).obj q) :
    mapAt T H q (oldWord T q p) = (homMap F x y).app q p := by
  have h := congrArg (fun f : C ⟶ D => homMap f x y) hH
  rw [homMap_comp, homMap_oldMap] at h
  exact congrArg (fun f => f.app q p) h

/-- The actual target-generator equation determines every same individual normalized new-letter map. -/
theorem mapAt_generator (T : Data C) (H : object T ⟶ D)
    (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (hH : ∀ x y, newHom T x y ≫ homMap H x y = m x y)
    (q : SimplexCategoryᵒᵖ) {x y : O} (g : newAt T q x y) :
    mapAt T H q (@generator O (scalarCategory C q) (newAt T q) x y g) = (m x y).app q g.val := by
  have h := congrArg (fun f => f.app q g.val) (hH x y)
  change mapAt T H q (letter T q g.val) = (m x y).app q g.val at h
  rw [letter_new] at h
  exact h

/-- The two actual enriched leg equations recover the entire original normalized-word evaluation. -/
theorem mapAt_eq_evalAt (T : Data C) (F : C ⟶ D) (H : object T ⟶ D)
    (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (hOld : oldMap T ≫ H = F) (hNew : ∀ x y, newHom T x y ≫ homMap H x y = m x y)
    (q : SimplexCategoryᵒᵖ) {x y : O} (p : WordAt T q x y) : mapAt T H q p = evalAt T F m q p := by
  induction p with
  | @old x y p => exact mapAt_old T F H hOld q p
  | @cons a x y b h g p ih =>
      change mapAt T H q (consWord T q h g p) = evalAt T F m q (consWord T q h g p)
      rw [mapAt_cons, evalAt_cons, mapAt_old T F H hOld,
        mapAt_generator T H m hNew, ih]

/-- The actual compatible normalized-word extension is unique as a whole original enriched map. -/
theorem desc_unique (T : Data C) (F : C ⟶ D)
    (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (hm : ∀ x y : O, T.inclusion x y ≫ m x y = T.attaching x y ≫ homMap F x y)
    (H : object T ⟶ D) (hOld : oldMap T ≫ H = F)
    (hNew : ∀ x y, newHom T x y ≫ homMap H x y = m x y) : H = desc T F m hm := by
  apply homMaps_ext
  intro x y
  rw [homMap_desc]
  ext q p
  exact mapAt_eq_evalAt T F H m hOld hNew q p

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
