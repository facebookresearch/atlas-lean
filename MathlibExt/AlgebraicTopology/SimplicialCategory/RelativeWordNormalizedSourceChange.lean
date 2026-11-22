/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordSourceShapeBoundaries
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordZeroLayer

/-!
# Literal original normalized words under SAME source change

The original two quivers and their inclusion are unchanged, so every
normalized target letter is the same original letter. Relabel every old
Hom segment by the unchanged original functor. Actual whole word
substitution retains exact finite length and both original raw operators.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords
variable {O : Type u} {C D : FixedObjects O}

/-- The literal normalized original source-word map retains every actual original new letter. -/
def normalizedSourceChange (T : Data C) (F : C ⟶ D) (q : SimplexCategoryᵒᵖ)
    {x y : O} (p : WordAt T q x y) : WordAt (sourceChange T F) q x y :=
  @relabel O (scalarCategory C q) (newAt T q) O (scalarCategory D q)
    (newAt (sourceChange T F) q) (scalarFunctor F q) (fun {_ _} g => g) x y p

/-- The SAME original normalized source-word map retains exact finite word length. -/
theorem normalizedSourceChange_length (T : Data C) (F : C ⟶ D) (q : SimplexCategoryᵒᵖ)
    {x y : O} (p : WordAt T q x y) :
    wordLength (sourceChange T F) q (normalizedSourceChange T F q p) = wordLength T q p :=
  @length_relabel O (scalarCategory C q) (newAt T q) O (scalarCategory D q)
    (newAt (sourceChange T F) q) (scalarFunctor F q) (fun {_ _} g => g) x y p

/-- The actual normalized map retains each full original cons decomposition. -/
theorem normalizedSourceChange_cons (T : Data C) (F : C ⟶ D) (q : SimplexCategoryᵒᵖ)
    {a x y b : O} (h : (hom C a x).obj q) (g : newAt T q x y) (p : WordAt T q y b) :
    normalizedSourceChange T F q (consWord T q h g p) =
      consWord (sourceChange T F) q ((homMap F a x).app q h) g (normalizedSourceChange T F q p) :=
  @relabel_cons O (scalarCategory C q) (newAt T q) O (scalarCategory D q)
    (newAt (sourceChange T F) q) (scalarFunctor F q) (fun {_ _} g => g) a x y b h g p

/-- The SAME original actual enriched source comparison reads every old Hom by the unchanged original functor. -/
theorem sourceChangeMap_old (T : Data C) (F : C ⟶ D) (q : SimplexCategoryᵒᵖ)
    {a b : O} (h : (hom C a b).obj q) :
    (homMap (sourceChangeMap T F) a b).app q (oldWord T q h) =
      oldWord (sourceChange T F) q ((homMap F a b).app q h) := by
  have hl : homMap (oldMap T) a b ≫ homMap (sourceChangeMap T F) a b =
      homMap F a b ≫ homMap (oldMap (sourceChange T F)) a b :=
    (homMap_comp (oldMap T) (sourceChangeMap T F) a b).symm.trans
      ((congrArg (fun k => homMap k a b) (oldMap_sourceChangeMap T F)).trans
        (homMap_comp F (oldMap (sourceChange T F)) a b))
  have hr : oldHom T a b ≫ homMap (sourceChangeMap T F) a b =
      homMap F a b ≫ oldHom (sourceChange T F) a b :=
    (congrArg (fun k => k ≫ homMap (sourceChangeMap T F) a b) (homMap_oldMap T a b)).symm.trans
      (hl.trans (congrArg (fun k => homMap F a b ≫ k) (homMap_oldMap (sourceChange T F) a b)))
  exact congrArg (fun k => k.app q h) hr


/-- Every complete original normalized source word equals the actual enriched source-map readback. -/
theorem normalizedSourceChange_readback (T : Data C) (F : C ⟶ D) (q : SimplexCategoryᵒᵖ)
    {a b : O} (p : WordAt T q a b) :
    normalizedSourceChange T F q p = (homMap (sourceChangeMap T F) a b).app q p := by
  induction p with
  | @old a b h => exact (sourceChangeMap_old T F q h).symm
  | @cons a x y b h g p ih =>
    let M (i j : O) : WordAt T q i j → WordAt (sourceChange T F) q i j :=
      fun p => (homMap (sourceChangeMap T F) i j).app q p
    have hcomp {i j k : O} (p : WordAt T q i j) (r : WordAt T q j k) :
        M i k (compWords T q p r) = compWords (sourceChange T F) q (M i j p) (M j k r) :=
      congrArg (fun h => h.app q (p, r)) (compositionMap_homMap (sourceChangeMap T F) i j k)
    have hgen : M x y (letter T q g.val) = letter (sourceChange T F) q g.val :=
      congrArg (fun k => k.app q g.val) (newHom_sourceChangeMap T F x y)
    have hgen' : M x y (@generator O (scalarCategory C q) (newAt T q) x y g) =
        @generator O (scalarCategory D q) (newAt (sourceChange T F) q) x y g := by
      have h1 := letter_new T q g
      have h2 := letter_new (sourceChange T F) q g
      exact (congrArg (M x y) h1).symm.trans (hgen.trans h2)
    have hold : M a x (oldWord T q h) = oldWord (sourceChange T F) q ((homMap F a x).app q h) :=
      sourceChangeMap_old T F q h
    have hcons := @cons_eq_comp O (scalarCategory C q) (newAt T q) a x y b h g p
    have hm : M a b (consWord T q h g p) = consWord (sourceChange T F) q
        ((homMap F a x).app q h) g (M y b p) := by
      exact (congrArg (M a b) hcons).trans
        ((hcomp _ _).trans
          ((congrArg (fun v => compWords (sourceChange T F) q v (M y b p)) (hcomp _ _)).trans (by
            rw [hold, hgen']
            exact (@cons_eq_comp O (scalarCategory D q) (newAt (sourceChange T F) q)
              a x y b ((homMap F a x).app q h) g (M y b p)).symm)))
    exact (normalizedSourceChange_cons T F q h g p).trans
      ((congrArg (fun p => consWord (sourceChange T F) q ((homMap F a x).app q h) g p) ih).trans hm.symm)

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
