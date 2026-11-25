/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.LexicographicLocalColimits
public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.LexicographicEndpoint
public import Mathlib.Order.Interval.Set.SuccPred

/-!
# Original outer-limit colimits and whole lexicographic continuity

Retain every original prefix vertex, inner map, endpoint leg and successor
transport, then construct the original flat outer-limit colimit and continuity.
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

/-- The exact original inner vertices preceding an original outer limit. -/
abbrev beforeOuter (j : J) : Set.Iio j → Type w' := fun i => K i.1

/-- The original outer-limit prefix diagram. -/
def outerPrefix (j : J) : Set.Iio j ⥤ C :=
  (Set.principalSegIio j).monotone.functor ⋙ F

/-- An original inner history below an outer limit is also a history of its exact restricted
successor. -/
noncomputable def outerPrefixInner (j : J) (hj : Order.IsSuccLimit j) (i : Set.Iio j) :
    TransfiniteCompositionOfShape (K i.1)
      ((outerPrefix F j).map (homOfLE (Order.le_succ i))) := by
  have hs : (Order.succ i).1 = Order.succ i.1 :=
    coe_succ_of_mem (hj.succ_lt i.2)
  let pointIso : F.obj (Order.succ i.1) ≅ F.obj (Order.succ i).1 :=
    F.mapIso (eqToIso hs.symm)
  exact
    { F := (c i.1).F
      isoBot := (c i.1).isoBot
      isWellOrderContinuous := (c i.1).isWellOrderContinuous
      incl := (c i.1).incl ≫ (Functor.const (K i.1)).map pointIso.hom
      isColimit := IsColimit.ofIsoColimit (c i.1).isColimit (Cocone.ext pointIso)
      fac := by
        change (c i.1).isoBot.inv ≫ ((c i.1).incl.app ⊥ ≫ F.map (eqToHom hs.symm)) =
          F.map ((Set.principalSegIio j).monotone.functor.map (homOfLE (Order.le_succ i)))
        rw [← Category.assoc, (c i.1).fac, ← F.map_comp]
        exact congrArg F.map (Subsingleton.elim _ _) }

/-- Restricting the outer order retains every original inner vertex and transition. -/
theorem outerPrefixInner_diagram (j : J) (hj : Order.IsSuccLimit j) (i : Set.Iio j) :
    (outerPrefixInner F c j hj i).F = (c i.1).F := rfl

/-- Its endpoint leg uses the actual original successor equality isomorphism. -/
theorem outerPrefixInner_incl (j : J) (hj : Order.IsSuccLimit j) (i : Set.Iio j) (k : K i.1) :
    (outerPrefixInner F c j hj i).incl.app k =
      (c i.1).incl.app k ≫ F.map (eqToHom
        (coe_succ_of_mem (hj.succ_lt i.2)).symm) := rfl

/-- Its bottom comparison is the original supplied inner bottom comparison. -/
theorem outerPrefixInner_isoBot (j : J) (hj : Order.IsSuccLimit j) (i : Set.Iio j) :
    (outerPrefixInner F c j hj i).isoBot = (c i.1).isoBot := rfl

/-- The exact flattened strict prefix reindexes by the original outer strict prefix. -/
def outerLimitIndexIso (j : J) :
    Index (beforeOuter (K := K) j) ≃o Set.Iio (vertex j (⊥ : K j)) where
  toFun a := ⟨vertex (ofLex a).1.1 (ofLex a).2,
    Sigma.Lex.left _ _ (ofLex a).1.2⟩
  invFun b := by
    rcases b with ⟨⟨i, k⟩, hb⟩
    have hi : i < j := by
      obtain h | ⟨he, hb⟩ := Sigma.Lex.lt_def.mp hb
      · exact h
      · change i = j at he
        subst i
        exact (not_lt_of_ge bot_le hb).elim
    exact toLex ⟨⟨i, hi⟩, k⟩
  left_inv a := by
    rcases a with ⟨⟨i, hi⟩, k⟩
    rfl
  right_inv b := by
    rcases b with ⟨⟨i, k⟩, hb⟩
    rfl
  map_rel_iff' := by
    intro a b
    rcases a with ⟨⟨i, hi⟩, k⟩
    rcases b with ⟨⟨m, hm⟩, l⟩
    constructor
    · intro h
      cases h with
      | left k l him => exact Sigma.Lex.left _ _ him
      | right k l hkl => exact Sigma.Lex.right _ _ hkl
    · intro h
      cases h with
      | left k l him => exact Sigma.Lex.left _ _ him
      | right k l hkl => exact Sigma.Lex.right _ _ hkl

omit [SuccOrder J] [∀ j, SuccOrder (K j)] [∀ j, WellFoundedLT (K j)] in
/-- Every original inner vertex is retained by the outer-limit reindexing. -/
theorem outerLimitIndexIso_vertex (j : J) (i : Set.Iio j) (k : K i.1) :
    (outerLimitIndexIso (K := K) j) (vertex i k) =
      ⟨vertex i.1 k, Sigma.Lex.left _ _ i.2⟩ := rfl

/-- The full original outer-limit prefix diagram is the same flattened inner diagram after
reindexing. -/
noncomputable def outerLimitDiagramIso (j : J) (hj : Order.IsSuccLimit j) :
    (outerLimitIndexIso (K := K) j).equivalence.functor ⋙
      (Set.principalSegIio (vertex j (⊥ : K j))).monotone.functor ⋙ diagram F c ≅
      diagram (outerPrefix F j) (outerPrefixInner F c j hj) :=
  NatIso.ofComponents (fun a => Iso.refl _) (by
    intro a b f
    rcases a with ⟨⟨i, hi⟩, k⟩
    rcases b with ⟨⟨m, hm⟩, l⟩
    have hf := leOfHom f
    cases hf with
    | right k l hkl =>
      change indexMap F c (vertex i k) (vertex i l) (Sigma.Lex.right _ _ hkl) ≫ 𝟙 _ =
        (𝟙 _) ≫ indexMap (outerPrefix F j) (outerPrefixInner F c j hj)
          (vertex (⟨i, hi⟩ : Set.Iio j) k) (vertex (⟨i, hi⟩ : Set.Iio j) l)
              (Sigma.Lex.right _ _ hkl)
      exact (congrArg (fun t => t ≫ 𝟙 _)
          (indexMap_inner F c i hkl)).trans
        ((Category.comp_id _).trans
          ((Category.id_comp _).symm.trans
            (congrArg (fun t => (𝟙 _) ≫ t)
              (indexMap_inner (outerPrefix F j) (outerPrefixInner F c j hj)
                (⟨i, hi⟩ : Set.Iio j) hkl)).symm))
    | left k l him =>
      change indexMap F c (vertex i k) (vertex m l) (Sigma.Lex.left _ _ him) ≫ 𝟙 _ =
        (𝟙 _) ≫ indexMap (outerPrefix F j) (outerPrefixInner F c j hj)
          (vertex (⟨i, hi⟩ : Set.Iio j) k) (vertex (⟨m, hm⟩ : Set.Iio j) l) (Sigma.Lex.left _ _ him)
      rw [indexMap_cross F c him,
        indexMap_cross (outerPrefix F j) (outerPrefixInner F c j hj) him]
      change crossMap F c him k l ≫ (𝟙 _) =
        (𝟙 _) ≫ crossMap (outerPrefix F j) (outerPrefixInner F c j hj) him k l
      have hc : crossMap (outerPrefix F j) (outerPrefixInner F c j hj) him k l =
          crossMap F c him k l := by
        have hsi : (Order.succ (⟨i, hi⟩ : Set.Iio j)).1 = Order.succ i :=
          coe_succ_of_mem (hj.succ_lt hi)
        dsimp only [crossMap, innerRoot]
        rw [outerPrefixInner_incl, outerPrefixInner_isoBot]
        change ((c i).incl.app k ≫ F.map (eqToHom
          hsi.symm)) ≫
          F.map (homOfLE (show (Order.succ (⟨i, hi⟩ : Set.Iio j)).1 ≤ m from
            Order.succ_le_of_lt him)) ≫ (c m).isoBot.inv ≫ (c m).F.map (homOfLE bot_le) =
          (c i).incl.app k ≫ F.map (homOfLE (Order.succ_le_of_lt (show i < m from him))) ≫
            (c m).isoBot.inv ≫ (c m).F.map (homOfLE bot_le)
        rw [Category.assoc, ← F.map_comp_assoc]
        have e : eqToHom hsi.symm ≫
            homOfLE (show (Order.succ (⟨i, hi⟩ : Set.Iio j)).1 ≤ m from Order.succ_le_of_lt him) =
            homOfLE (Order.succ_le_of_lt (show i < m from him)) := Subsingleton.elim _ _
        rw [e]
      exact (Category.comp_id _).trans
        ((congrArg (fun t => (𝟙 _) ≫ t) hc).trans (Category.id_comp _)).symm)

/-- The original outer principal colimit yields the exact flat outer-limit principal colimit. -/
noncomputable def outerLimitIsColimit [F.IsWellOrderContinuous] (j : J)
    (hj : Order.IsSuccLimit j) :
    IsColimit ((Set.principalSegIio (vertex j (⊥ : K j))).cocone (diagram F c)) := by
  let E := (outerLimitIndexIso (K := K) j).equivalence
  let original := (Set.principalSegIio j).cocone F
  let inner := outerPrefixInner F c j hj
  let originalColimit := F.isColimitOfIsWellOrderContinuous j hj
  let normalized := endpoint (outerPrefix F j) inner original.ι
  let normalizedColimit := endpointIsColimit (outerPrefix F j) inner original.ι originalColimit
  let flat := ((Set.principalSegIio (vertex j (⊥ : K j))).cocone (diagram F c)).whisker E.functor
  let e := outerLimitDiagramIso F c j hj
  let pointIso : F.obj j ≅ (diagram F c).obj (vertex j (⊥ : K j)) := (c j).isoBot.symm
  apply (Functor.Final.isColimitWhiskerEquiv E.functor _).1
  apply (IsColimit.precomposeHomEquiv e.symm flat).1
  exact IsColimit.ofIsoColimit normalizedColimit (Cocone.ext pointIso (by
    intro a
    rcases a with ⟨⟨i, hi⟩, k⟩
    have hsi : (Order.succ (⟨i, hi⟩ : Set.Iio j)).1 = Order.succ i :=
      coe_succ_of_mem (hj.succ_lt hi)
    change ((inner ⟨i, hi⟩).incl.app k ≫
      F.map (homOfLE (show (Order.succ (⟨i, hi⟩ : Set.Iio j)).1 ≤ j from
        (Order.succ (⟨i, hi⟩ : Set.Iio j)).2.le))) ≫ pointIso.hom =
      e.symm.hom.app (vertex (⟨i, hi⟩ : Set.Iio j) k) ≫
        indexMap F c (vertex i k) (vertex j (⊥ : K j)) (Sigma.Lex.left _ _ hi)
    have heapp : e.symm.hom.app (vertex (⟨i, hi⟩ : Set.Iio j) k) = 𝟙 ((c i).F.obj k) := rfl
    have hroot : innerRoot F c j (⊥ : K j) = pointIso.hom := by
      dsimp only [innerRoot]
      have h : homOfLE (bot_le : (⊥ : K j) ≤ ⊥) = 𝟙 (⊥ : K j) := Subsingleton.elim _ _
      rw [h, Functor.map_id, Category.comp_id]
      rfl
    have hm : eqToHom hsi.symm ≫
        homOfLE (show (Order.succ (⟨i, hi⟩ : Set.Iio j)).1 ≤ j from
          (Order.succ (⟨i, hi⟩ : Set.Iio j)).2.le) =
        homOfLE (Order.succ_le_of_lt hi) := Subsingleton.elim _ _
    rw [heapp, indexMap_cross F c hi, outerPrefixInner_incl]
    dsimp only [crossMap]
    rw [hroot]
    have hmaps : F.map (eqToHom hsi.symm) ≫
        F.map (homOfLE (show (Order.succ (⟨i, hi⟩ : Set.Iio j)).1 ≤ j from
          (Order.succ (⟨i, hi⟩ : Set.Iio j)).2.le)) =
        F.map (homOfLE (Order.succ_le_of_lt hi)) :=
      (F.map_comp _ _).symm.trans (congrArg F.map hm)
    have whole : (((c i).incl.app k ≫ F.map (eqToHom hsi.symm)) ≫
        F.map (homOfLE (show (Order.succ (⟨i, hi⟩ : Set.Iio j)).1 ≤ j from
          (Order.succ (⟨i, hi⟩ : Set.Iio j)).2.le))) ≫ (c j).isoBot.inv =
        (c i).incl.app k ≫ F.map (homOfLE (Order.succ_le_of_lt hi)) ≫ (c j).isoBot.inv := by
      have hleft := congrArg (fun t => (c i).incl.app k ≫ t) hmaps
      have hall := congrArg (fun t => t ≫ (c j).isoBot.inv) hleft
      have hassoc := congrArg (fun t => t ≫ (c j).isoBot.inv)
        (Category.assoc ((c i).incl.app k) (F.map (eqToHom hsi.symm))
          (F.map (homOfLE (show (Order.succ (⟨i, hi⟩ : Set.Iio j)).1 ≤ j from
            (Order.succ (⟨i, hi⟩ : Set.Iio j)).2.le))))
      exact (hassoc.trans hall).trans (Category.assoc _ _ _)
    exact whole.trans (Category.id_comp _).symm))

variable [OrderBot J] [WellFoundedLT J]

/-- The entire original variable-inner lexicographic diagram is well-order continuous. -/
theorem diagramIsWellOrderContinuous [F.IsWellOrderContinuous] :
    (diagram F c).IsWellOrderContinuous where
  nonempty_isColimit a ha := by
    classical
    rcases a with ⟨j, k⟩
    by_cases hk : k = ⊥
    · subst k
      induction j using SuccOrder.limitRecOn with
      | isMin j hj =>
        obtain rfl := hj.eq_bot
        exact (ha.not_isMin (isMin_bot : IsMin (vertex (⊥ : J) (⊥ : K ⊥)))).elim
      | succ j hj ih =>
        exact ⟨successorBottomIsColimit F c j hj⟩
      | isSuccLimit j hj ih =>
        exact ⟨outerLimitIsColimit F c j hj⟩
    · exact ⟨innerLimitIsColimit F c j k hk ha⟩

end CategoryTheory.SmallObject.CellularNormalization
