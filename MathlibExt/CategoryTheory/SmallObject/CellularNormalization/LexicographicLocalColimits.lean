/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.LexicographicDiagram
public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.LexicographicOrder
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Local lexicographic prefixes inherit their original inner colimits

Construct true finality and exact colimit cocones for original nonbottom inner
limits and for the whole preceding block at an original successor bottom.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace CategoryTheory.SmallObject.CellularNormalization

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [LinearOrder J] [SuccOrder J]
variable {K : J → Type w'} [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)]
  [∀ j, OrderBot (K j)] [∀ j, WellFoundedLT (K j)]
variable (F : J ⥤ C)
variable (c : ∀ j, TransfiniteCompositionOfShape (K j)
  (F.map (homOfLE (Order.le_succ j))))

omit [SuccOrder J] [∀ j, SuccOrder (K j)] [∀ j, OrderBot (K j)]
  [∀ j, WellFoundedLT (K j)] in
/-- The original inner prefix sits monotonically in the exact flattened prefix. -/
theorem innerStrictPrefix_monotone (j : J) (k : K j) :
    Monotone (innerStrictPrefix (K := K) j k) :=
  fun _ _ h => Sigma.Lex.right _ _ h

omit [SuccOrder J] [∀ j, SuccOrder (K j)] [∀ j, WellFoundedLT (K j)] in
/-- For a nonbottom inner vertex its original strict prefix is actually cofinal. -/
theorem innerStrictPrefix_final (j : J) (k : K j) (hk : k ≠ ⊥) :
    (innerStrictPrefix_monotone (K := K) j k).functor.Final := by
  classical
  let _ : Nonempty (Set.Iio k) := ⟨⟨⊥, bot_lt_iff_ne_bot.mpr hk⟩⟩
  apply Functor.final_of_exists_of_isFiltered
  · rintro ⟨⟨i, l⟩, h⟩
    cases h with
    | left l k hij =>
      exact ⟨⟨⊥, bot_lt_iff_ne_bot.mpr hk⟩, ⟨homOfLE (Sigma.Lex.left _ _ hij)⟩⟩
    | right l k hl =>
      exact ⟨⟨l, hl⟩, ⟨𝟙 _⟩⟩
  · intro d l s t
    exact ⟨l, 𝟙 _, Subsingleton.elim _ _⟩

/-- The original inner limit colimit supplies the exact flat principal-prefix colimit. -/
noncomputable def innerLimitIsColimit (j : J) (k : K j) (hk : k ≠ ⊥)
    (hlim : Order.IsSuccLimit ((toLex ⟨j, k⟩) : Index K)) :
    IsColimit ((Set.principalSegIio ((toLex ⟨j, k⟩) : Index K)).cocone (diagram F c)) := by
  let _ : (innerStrictPrefix_monotone (K := K) j k).functor.Final :=
    innerStrictPrefix_final (K := K) j k hk
  apply (Functor.Final.isColimitWhiskerEquiv
    (innerStrictPrefix_monotone (K := K) j k).functor _).1
  let U := (innerStrictPrefix_monotone (K := K) j k).functor
  let S := (Set.principalSegIio (vertex j k)).monotone.functor
  let T := (Set.principalSegIio k).monotone.functor
  let e : U ⋙ S ⋙ diagram F c ≅ T ⋙ (c j).F :=
    NatIso.ofComponents (fun l => (Iso.refl ((c j).F.obj l.1))) (by
      intro l m f
      change indexMap F c (vertex j l.1) (vertex j m.1)
        (Sigma.Lex.right _ _ (leOfHom f)) ≫ (𝟙 _) =
        (𝟙 _) ≫ (c j).F.map (homOfLE (leOfHom f))
      exact (congrArg (fun t => t ≫ 𝟙 _) (indexMap_inner F c j (leOfHom f))).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  let original := (c j).F.isColimitOfIsWellOrderContinuous k
    (inner_limit_of_flat_limit (K := K) hlim hk)
  let flat : Cocone (U ⋙ S ⋙ diagram F c) :=
    ((Set.principalSegIio (vertex j k)).cocone (diagram F c)).whisker U
  apply (IsColimit.precomposeHomEquiv e.symm flat).1
  let pointIso : (c j).F.obj k ≅ (diagram F c).obj (vertex j k) := Iso.refl _
  exact IsColimit.ofIsoColimit original (Cocone.ext pointIso (by
    intro l
    change (c j).F.map (homOfLE l.2.le) ≫ pointIso.hom =
      e.symm.hom.app l ≫ indexMap F c (vertex j l.1) (vertex j k) (Sigma.Lex.right _ _ l.2.le)
    have heapp : e.symm.hom.app l = (𝟙 ((c j).F.obj l.1)) := by
      dsimp [e]
      rfl
    have hm := indexMap_inner F c j l.2.le
    have lhs : (c j).F.map (homOfLE l.2.le) ≫ pointIso.hom =
        (c j).F.map (homOfLE l.2.le) := Category.comp_id _
    have rhs : e.symm.hom.app l ≫ indexMap F c (vertex j l.1) (vertex j k)
        (Sigma.Lex.right _ _ l.2.le) = (c j).F.map (homOfLE l.2.le) := by
      exact (congrArg (fun t => t ≫ indexMap F c (vertex j l.1) (vertex j k)
          (Sigma.Lex.right _ _ l.2.le)) heapp).trans ((Category.id_comp _).trans hm)
    exact lhs.trans rhs.symm))

/-- The entire preceding original block lies below the next original bottom. -/
def precedingBlock (j : J) (hj : ¬ IsMax j) : K j ⥤
    Set.Iio (vertex (Order.succ j) (⊥ : K (Order.succ j))) where
  obj k := ⟨vertex j k, Sigma.Lex.left _ _ (Order.lt_succ_iff_not_isMax.mpr hj)⟩
  map f := homOfLE (Sigma.Lex.right _ _ (leOfHom f))

omit [∀ j, SuccOrder (K j)] [∀ j, WellFoundedLT (K j)] in
/-- The original preceding block is genuinely final in that strict prefix. -/
theorem precedingBlock_final (j : J) (hj : ¬ IsMax j) : (precedingBlock (K := K) j hj).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · rintro ⟨⟨i, l⟩, hi⟩
    cases hi with
    | left l b hij =>
      have hji : i ≤ j := Order.le_of_lt_succ hij
      obtain rfl | hij := hji.eq_or_lt
      · exact ⟨l, ⟨𝟙 _⟩⟩
      · exact ⟨⊥, ⟨homOfLE (Sigma.Lex.left _ _ hij)⟩⟩
    | right l b hl => exact (not_lt_of_ge bot_le hl).elim
  · intro d l s t
    exact ⟨l, 𝟙 _, Subsingleton.elim _ _⟩

/-- The original inner endpoint colimit constructs the next-bottom prefix colimit. -/
noncomputable def successorBottomIsColimit (j : J) (hj : ¬ IsMax j) :
    IsColimit ((Set.principalSegIio (vertex (Order.succ j) (⊥ : K (Order.succ j)))).cocone
      (diagram F c)) := by
  let U := precedingBlock (K := K) j hj
  let S := (Set.principalSegIio (vertex (Order.succ j) (⊥ : K (Order.succ j)))).monotone.functor
  let _ : U.Final := precedingBlock_final (K := K) j hj
  apply (Functor.Final.isColimitWhiskerEquiv U _).1
  let e : U ⋙ S ⋙ diagram F c ≅ (c j).F :=
    NatIso.ofComponents (fun k => Iso.refl ((c j).F.obj k)) (by
      intro k l f
      change indexMap F c (vertex j k) (vertex j l) (Sigma.Lex.right k l (leOfHom f)) ≫ 𝟙 _ =
        (𝟙 _) ≫ (c j).F.map f
      exact (congrArg (fun t => t ≫ 𝟙 _) (indexMap_inner F c j (leOfHom f))).trans
        ((Category.comp_id _).trans
          ((congrArg (c j).F.map (Subsingleton.elim (homOfLE (leOfHom f)) f)).trans
            (Category.id_comp _).symm)))
  let flat := ((Set.principalSegIio (vertex (Order.succ j) (⊥ : K (Order.succ j)))).cocone
    (diagram F c)).whisker U
  apply (IsColimit.precomposeHomEquiv e.symm flat).1
  let pointIso : F.obj (Order.succ j) ≅
      (diagram F c).obj (vertex (Order.succ j) (⊥ : K (Order.succ j))) :=
    (c (Order.succ j)).isoBot.symm
  exact IsColimit.ofIsoColimit (c j).isColimit
    (Cocone.ext pointIso (by
      intro k
      change (c j).incl.app k ≫ pointIso.hom =
        e.symm.hom.app k ≫ indexMap F c (vertex j k) (vertex (Order.succ j) (⊥ : K (Order.succ j)))
          (Sigma.Lex.left _ _ (Order.lt_succ_iff_not_isMax.mpr hj))
      have heapp : e.symm.hom.app k = 𝟙 ((c j).F.obj k) := rfl
      have hmap : F.map (homOfLE (Order.succ_le_of_lt (Order.lt_succ_iff_not_isMax.mpr hj))) =
          𝟙 (F.obj (Order.succ j)) :=
        (congrArg F.map (Subsingleton.elim _ (𝟙 (Order.succ j)))).trans (F.map_id _)
      have hroot : innerRoot F c (Order.succ j) (⊥ : K (Order.succ j)) = pointIso.hom := by
        dsimp only [innerRoot]
        have e : homOfLE (bot_le : (⊥ : K (Order.succ j)) ≤ ⊥) = 𝟙 (⊥ : K (Order.succ j)) :=
          Subsingleton.elim _ _
        rw [e, Functor.map_id, Category.comp_id]
        rfl
      have hcross : crossMap F c (Order.lt_succ_iff_not_isMax.mpr hj) k ⊥ =
          (c j).incl.app k ≫ (c (Order.succ j)).isoBot.inv := by
        dsimp only [crossMap]
        rw [hmap]
        change (c j).incl.app k ≫ (𝟙 _) ≫ innerRoot F c (Order.succ j) ⊥ =
          (c j).incl.app k ≫ (c (Order.succ j)).isoBot.inv
        exact congrArg (fun t => (c j).incl.app k ≫ t)
          ((Category.id_comp _).trans hroot)
      exact (congrArg (fun t => e.symm.hom.app k ≫ t)
        (indexMap_cross F c (Order.lt_succ_iff_not_isMax.mpr hj) k ⊥)).trans
        ((congrArg (fun t => e.symm.hom.app k ≫ t) hcross).trans
          ((congrArg (fun t => t ≫ ((c j).incl.app k ≫ pointIso.hom)) heapp).trans
            (Category.id_comp _))) |>.symm))

end CategoryTheory.SmallObject.CellularNormalization
