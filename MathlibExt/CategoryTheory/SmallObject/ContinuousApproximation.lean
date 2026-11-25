/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Successors
public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Limits

/-!
# Continuous approximation from a fixed functorial factorization

This is the complete original category/order/factorization construction moved
from the native continuous-source approximation module. The original prefix
objects, successor squares, source-colimit limits, ordinal, factorization and
counit maps are retained. The prerequisites are category, order, colimit and
functorial factorization data.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v w uC vC

namespace CategoryTheory.OriginalContinuousApproximation

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  (F : J ⥤ C) (q0 : Arrow C) {P R : MorphismProperty C}
  (factor : MorphismProperty.FunctorialFactorizationData P R)

/-- The entire original successor square for an arbitrary current counit. -/
def successorSquare (j : J) (p : Arrow C) (e : p.right = F.obj j) :
    p ⟶ Arrow.mk ((factor.p.app (Arrow.mk
      (p.hom ≫ eqToHom e ≫ F.map (homOfLE (Order.le_succ j)))))) :=
  Arrow.homMk (factor.i.app (Arrow.mk (p.hom ≫ eqToHom e ≫
    F.map (homOfLE (Order.le_succ j)))))
    (eqToHom e ≫ F.map (homOfLE (Order.le_succ j))) (by
      change factor.i.app (Arrow.mk (p.hom ≫ eqToHom e ≫
        F.map (homOfLE (Order.le_succ j)))) ≫
        factor.p.app (Arrow.mk (p.hom ≫ eqToHom e ≫
          F.map (homOfLE (Order.le_succ j)))) = _
      exact factor.fac_app)

omit [OrderBot J] [WellFoundedLT J] [HasColimitsOfSize.{w, w} C] in
/-- Equality of the entire current counit preserves the same original factorization square. -/
theorem successorSquare_eq {j : J} {p p' : Arrow C} (hp : p = p')
    (e : p.right = F.obj j) (e' : p'.right = F.obj j) :
    Arrow.mk (successorSquare F factor j p e) =
      Arrow.mk (successorSquare F factor j p' e') := by
  cases hp
  rfl

/-- A canonical complete original prefix stores exact factory/limit arrows and
the original target functor, never desired weak equivalences or closure outcomes. -/
structure Prefix (j : J) where
  /-- All original approximation source/target objects, arrows and squares. -/
  D : Set.Iic j ⥤ Arrow C
  /-- The target projection is the caller's original restricted diagram on every map. -/
  target_eq : D ⋙ Arrow.rightFunc = (Set.initialSegIic j).monotone.functor ⋙ F
  /-- The original bottom arrow retains the complete same-factory source and counit. -/
  bottom_eq : D.obj ⟨⊥, bot_le⟩ = q0
  /-- Each complete original successor arrow square is the same original factory square. -/
  successor_eq (i : J) (hi : i < j) :
    Arrow.mk (D.map (homOfLE (Order.le_succ i) :
      ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩)) =
      Arrow.mk (successorSquare F factor i (D.obj ⟨i, hi.le⟩)
        (Functor.congr_obj target_eq ⟨i, hi.le⟩))
  /-- At each actual limit, all source leg arrows retain the real chosen preceding colimit. -/
  source_limit_eq (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j)
      (k : J) (hk : k < i) :
    Arrow.mk ((D.map (homOfLE hk.le : ⟨k, hk.le.trans hij⟩ ⟶ ⟨i, hij⟩)).left) =
      Arrow.mk (colimit.ι (SmallObject.restrictionLT (D ⋙ Arrow.leftFunc) hij) ⟨k, hk⟩)

end CategoryTheory.OriginalContinuousApproximation
namespace CategoryTheory.OriginalContinuousApproximation

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  {F : J ⥤ C} {q0 : Arrow C} {P R : MorphismProperty C}
  {factor : MorphismProperty.FunctorialFactorizationData P R}

namespace Prefix

/-- The complete canonical prefix restricts with the same original source and target maps. -/
def restrict {j k : J} (S : Prefix F q0 factor k) (h : j ≤ k) : Prefix F q0 factor j where
  D := SmallObject.restrictionLE S.D h
  target_eq := by
    change (Set.initialSegIicIicOfLE h).monotone.functor ⋙ (S.D ⋙ Arrow.rightFunc) = _
    rw [S.target_eq]
    rfl
  bottom_eq := S.bottom_eq
  successor_eq i hi := S.successor_eq i (lt_of_lt_of_le hi h)
  source_limit_eq i hi hij k hk := S.source_limit_eq i hi (hij.trans h) k hk

omit [WellFoundedLT J] in
@[ext]
theorem ext {j : J} {S T : Prefix F q0 factor j} (hD : S.D = T.D) : S = T := by
  cases S
  cases T
  cases hD
  rfl

omit [WellFoundedLT J] in
/-- Restriction at the same endpoint keeps the entire original prefix. -/
theorem restrict_id {j : J} (S : Prefix F q0 factor j) : S.restrict le_rfl = S := by
  apply ext
  rfl

omit [WellFoundedLT J] in
/-- Two actual prefix restrictions keep their literal complete composition. -/
theorem restrict_comp {i j k : J} (S : Prefix F q0 factor k) (hij : i ≤ j) (hjk : j ≤ k) :
    (S.restrict hjk).restrict hij = S.restrict (hij.trans hjk) := by
  apply ext
  rfl

/-- The bottom prefix is the exact supplied original I-Q counit arrow. -/
def bottom (hq0 : q0.right = F.obj ⊥) : Prefix F q0 factor (⊥ : J) where
  D := (Functor.const _).obj q0
  target_eq := by
    apply Functor.hext
    · intro i
      obtain rfl : i = (⟨⊥,le_rfl⟩ : Set.Iic (⊥ : J)) :=
        Subtype.ext (le_antisymm i.2 bot_le)
      exact hq0
    · intro i j f
      obtain rfl : i = (⟨⊥,le_rfl⟩ : Set.Iic (⊥ : J)) :=
        Subtype.ext (le_antisymm i.2 bot_le)
      obtain rfl : j = (⟨⊥,le_rfl⟩ : Set.Iic (⊥ : J)) :=
        Subtype.ext (le_antisymm j.2 bot_le)
      obtain rfl : f = 𝟙 (⟨⊥,le_rfl⟩ : Set.Iic (⊥ : J)) := Subsingleton.elim _ _
      simp only [Functor.map_id]
      exact hq0 ▸ HEq.rfl
  bottom_eq := rfl
  successor_eq i hi := (not_lt_bot hi).elim
  source_limit_eq i hi hij := by
    obtain rfl : i = ⊥ := le_antisymm hij bot_le
    exact (Order.not_isSuccLimit_bot hi).elim

end Prefix

end CategoryTheory.OriginalContinuousApproximation

namespace CategoryTheory.OriginalContinuousApproximation

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.SuccStruct

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  {F : J ⥤ C} {q0 : Arrow C} {P R : MorphismProperty C}
  {factor : MorphismProperty.FunctorialFactorizationData P R}

namespace Prefix

/-- The entire successor square is the same original factory square at the current top. -/
def nextMap {j : J} (S : Prefix F q0 factor j) :=
  successorSquare F factor j (S.D.obj ⟨j, le_rfl⟩)
    (Functor.congr_obj S.target_eq ⟨j, le_rfl⟩)

/-- The complete canonical successor Arrow diagram is the actual pinned extension. -/
def successorDiagram {j : J} (S : Prefix F q0 factor j) (hj : ¬IsMax j) :
    Set.Iic (Order.succ j) ⥤ Arrow C := extendToSucc hj S.D S.nextMap

omit [WellFoundedLT J] in
/-- The entire predecessor is retained exactly in the successor Arrow diagram. -/
theorem successorDiagram_restrict {j : J} (S : Prefix F q0 factor j) (hj : ¬IsMax j) :
    SmallObject.restrictionLE (S.successorDiagram hj) (Order.le_succ j) = S.D :=
  extendToSucc_restrict_eq hj S.D S.nextMap

omit [WellFoundedLT J] in
/-- The entire original target F is retained by the complete next prefix. -/
theorem successorDiagram_target {j : J} (S : Prefix F q0 factor j) (hj : ¬IsMax j) :
    S.successorDiagram hj ⋙ Arrow.rightFunc =
      (Set.initialSegIic (Order.succ j)).monotone.functor ⋙ F := by
  rw [successorDiagram, extendToSucc_comp]
  change extendToSucc hj (S.D ⋙ Arrow.rightFunc)
    (eqToHom (Functor.congr_obj S.target_eq ⟨j, le_rfl⟩) ≫
      F.map (homOfLE (Order.le_succ j))) = _
  exact (extendToSucc_precompose_eq hj (S.D ⋙ Arrow.rightFunc) S.target_eq
    (F.map (homOfLE (Order.le_succ j)))).trans (extendToSucc_original_eq hj F)

omit [WellFoundedLT J] in
/-- The original bottom Arrow remains unchanged after the genuine successor extension. -/
theorem successorDiagram_bottom {j : J} (S : Prefix F q0 factor j) (hj : ¬IsMax j) :
    (S.successorDiagram hj).obj ⟨⊥, bot_le⟩ = q0 :=
  (Functor.congr_obj (S.successorDiagram_restrict hj) (⟨⊥, bot_le⟩ : Set.Iic j)).trans S.bottom_eq

end Prefix

end CategoryTheory.OriginalContinuousApproximation

namespace CategoryTheory.OriginalContinuousApproximation.Prefix

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.SuccStruct

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  {F : J ⥤ C} {q0 : Arrow C} {P R : MorphismProperty C}
  {factor : MorphismProperty.FunctorialFactorizationData P R}

omit [WellFoundedLT J] in
/-- Every old successor square remains the same original whole factory square. -/
theorem successorDiagram_successor_eq {j : J} (S : Prefix F q0 factor j) (hj : ¬IsMax j)
    (i : J) (hi : i < Order.succ j) :
    Arrow.mk ((S.successorDiagram hj).map (homOfLE (Order.le_succ i) :
      ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩)) =
      Arrow.mk (successorSquare F factor i ((S.successorDiagram hj).obj ⟨i, hi.le⟩)
        (Functor.congr_obj (S.successorDiagram_target hj) ⟨i, hi.le⟩)) := by
  have hi' : i ≤ j := (Order.lt_succ_iff_of_not_isMax hj).mp hi
  obtain hi' | hij := hi'.lt_or_eq
  · have hRestrict := S.successorDiagram_restrict hj
    have hMap := arrowMap_extendToSucc hj S.D S.nextMap i (Order.succ i)
      (Order.le_succ i) (Order.succ_le_of_lt hi')
    change Arrow.mk ((S.successorDiagram hj).map (homOfLE (Order.le_succ i))) =
      Arrow.mk (S.D.map (homOfLE (Order.le_succ i))) at hMap
    calc
      _ = Arrow.mk (S.D.map (homOfLE (Order.le_succ i))) := hMap
      _ = Arrow.mk (successorSquare F factor i (S.D.obj ⟨i, hi'.le⟩)
          (Functor.congr_obj S.target_eq ⟨i, hi'.le⟩)) := S.successor_eq i hi'
      _ = _ := by
        have he := extendToSucc_obj_eq hj S.D S.nextMap i hi'.le
        change (S.successorDiagram hj).obj ⟨i, hi.le⟩ = S.D.obj ⟨i, hi'.le⟩ at he
        exact successorSquare_eq F factor he.symm _ _
  · subst i
    have h := arrowSucc_extendToSucc hj S.D S.nextMap
    change Arrow.mk ((S.successorDiagram hj).map (homOfLE (Order.le_succ j))) = _ at h
    calc
      _ = Arrow.mk S.nextMap := h
      _ = _ := by
        have he := extendToSucc_obj_eq hj S.D S.nextMap j le_rfl
        change (S.successorDiagram hj).obj ⟨j, hi.le⟩ = S.D.obj ⟨j, le_rfl⟩ at he
        exact successorSquare_eq F factor he.symm _ _

end CategoryTheory.OriginalContinuousApproximation.Prefix

namespace CategoryTheory.OriginalContinuousApproximation

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  (F : J ⥤ C) (q0 : Arrow C) {P R : MorphismProperty C}
  (factor : MorphismProperty.FunctorialFactorizationData P R)

/-- The actual canonical prefix inverse system retains every original restriction. -/
def prefixFunctor : Jᵒᵖ ⥤ Type (max w uC vC) where
  obj j := Prefix F q0 factor j.unop
  map f := ↾fun S => S.restrict (leOfHom f.unop)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro S
    exact S.restrict_id
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro S
    exact (S.restrict_comp (leOfHom g.unop) (leOfHom f.unop)).symm

namespace Glue

variable {F q0 factor}
  (U : LowerSet J)
  (x : ((OrderHom.Subtype.val (fun j : J => j ∈ (U : Set J))).monotone.functor.op ⋙
    prefixFunctor F q0 factor).sections)

/-- The complete original canonical prefix at an actual lower-carrier label. -/
def state (i : (U : Set J)) : Prefix F q0 factor i.1 := x.val (Opposite.op i)

omit [WellFoundedLT J] in
/-- Section compatibility is literal equality of the whole canonical prefix. -/
theorem restrict_state {i j : (U : Set J)} (h : i ≤ j) :
    (state U x j).restrict h = state U x i := x.property (homOfLE h).op

/-- Each original actual Arrow object is read from its own canonical prefix. -/
def object (i : (U : Set J)) : Arrow C := (state U x i).D.obj ⟨i.1, le_rfl⟩

omit [WellFoundedLT J] in
/-- The same original object is retained in every later canonical prefix. -/
theorem object_in_larger {i j : (U : Set J)} (h : i ≤ j) :
    (state U x j).D.obj ⟨i.1, h⟩ = object U x i :=
  Functor.congr_obj (congrArg Prefix.D (restrict_state U x h)) ⟨i.1, le_rfl⟩

/-- The full original Arrow square is computed in the larger canonical prefix. -/
def stageMap {i j : (U : Set J)} (h : i ≤ j) : object U x i ⟶ object U x j :=
  eqToHom (object_in_larger U x h).symm ≫
    (state U x j).D.map (homOfLE h : (⟨i.1, h⟩ : Set.Iic j.1) ⟶ ⟨j.1, le_rfl⟩)

omit [WellFoundedLT J] in
/-- Every whole original square is identical to its map in any later complete prefix. -/
theorem stageMap_heq_in_larger {i j k : (U : Set J)} (hij : i ≤ j) (hjk : j ≤ k) :
    stageMap U x hij ≍ (state U x k).D.map
      (homOfLE hij : ⟨i.1, hij.trans hjk⟩ ⟶ ⟨j.1, hjk⟩) := by
  have h0 : stageMap U x hij ≍ (state U x j).D.map
      (homOfLE hij : (⟨i.1, hij⟩ : Set.Iic j.1) ⟶ ⟨j.1, le_rfl⟩) := by
    change eqToHom (object_in_larger U x hij).symm ≫
      (state U x j).D.map (homOfLE hij) ≍ (state U x j).D.map (homOfLE hij)
    exact eqToHom_comp_heq _ _
  exact h0.trans (Functor.hcongr_hom
    (congrArg Prefix.D (restrict_state U x hjk)).symm (homOfLE hij))

omit [WellFoundedLT J] in
/-- The same-label whole Arrow map is the actual identity. -/
theorem stageMap_refl (i : (U : Set J)) : stageMap U x (le_refl i) = 𝟙 (object U x i) := by
  have h := stageMap_heq_in_larger U x (le_refl i) (le_refl i)
  exact eq_of_heq (h.trans (heq_of_eq ((state U x i).D.map_id ⟨i.1, le_rfl⟩)))

omit [WellFoundedLT J] in
/-- Every composition is verified in the same complete original terminal prefix. -/
theorem stageMap_comp {i j k : (U : Set J)} (hij : i ≤ j) (hjk : j ≤ k) :
    stageMap U x (hij.trans hjk) = stageMap U x hij ≫ stageMap U x hjk := by
  let f : (⟨i.1, hij.trans hjk⟩ : Set.Iic k.1) ⟶ ⟨j.1, hjk⟩ := homOfLE hij
  let g : (⟨j.1, hjk⟩ : Set.Iic k.1) ⟶ ⟨k.1, le_rfl⟩ := homOfLE hjk
  have hF := stageMap_heq_in_larger U x hij hjk
  have hG := stageMap_heq_in_larger U x hjk (le_refl k)
  have hFG := stageMap_heq_in_larger U x (hij.trans hjk) (le_refl k)
  have hComp := heq_comp (object_in_larger U x (hij.trans hjk)).symm
    (object_in_larger U x hjk).symm (object_in_larger U x (le_refl k)).symm hF hG
  exact eq_of_heq ((hFG.trans (heq_of_eq ((state U x k).D.map_comp f g))).trans hComp.symm)

/-- Compatible full original prefixes construct an actual Arrow diagram on the
same lower carrier. -/
def diagram : (U : Set J) ⥤ Arrow C where
  obj := object U x
  map f := stageMap U x (leOfHom f)
  map_id i := stageMap_refl U x i
  map_comp f g := stageMap_comp U x (leOfHom f) (leOfHom g)

/-- Every original closed prefix is included in the same actual lower carrier. -/
def prefixInclusion (i : (U : Set J)) : Set.Iic i.1 →o (U : Set J) where
  toFun j := ⟨j.1, U.lower j.2 i.2⟩
  monotone' _ _ h := h

omit [WellFoundedLT J] in
/-- The complete canonical predecessor, including all Arrow maps, is recovered literally. -/
theorem diagram_restrict (i : (U : Set J)) :
    (prefixInclusion U i).monotone.functor ⋙ diagram U x = (state U x i).D := by
  apply Functor.hext
  · intro j
    exact (object_in_larger U x (show prefixInclusion U i j ≤ i from j.2)).symm
  · intro a b f
    exact stageMap_heq_in_larger U x
      (show prefixInclusion U i a ≤ prefixInclusion U i b from leOfHom f)
      (show prefixInclusion U i b ≤ i from b.2)

end Glue

end CategoryTheory.OriginalContinuousApproximation

namespace CategoryTheory.OriginalContinuousApproximation.Prefix

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

theorem map_eq_of_arrow_eq {D : Type uC} [Category.{vC} D]
    {A X Y : D} (f : A ⟶ X) (g : A ⟶ Y) (e : X = Y)
    (h : Arrow.mk f = Arrow.mk g) : g ≫ eqToHom e.symm = f := by
  obtain ⟨hs, ht, hm⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  have hId : eqToHom hs = 𝟙 A := eqToHom_refl A hs
  have hf : f = g ≫ eqToHom ht.symm := by
    calc
      f = eqToHom hs ≫ g ≫ eqToHom ht.symm := hm
      _ = 𝟙 A ≫ g ≫ eqToHom ht.symm :=
        congrArg (fun q : A ⟶ A => q ≫ g ≫ eqToHom ht.symm) hId
      _ = g ≫ eqToHom ht.symm := by rw [Category.id_comp]
  exact hf.symm

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  {F : J ⥤ C} {q0 : Arrow C} {P R : MorphismProperty C}
  {factor : MorphismProperty.FunctorialFactorizationData P R}

/-- The exact source limit Arrow equations imply the genuine source colimit at every
original limit prefix; no input source continuity proof is supplied. -/
def sourceIsColimit {j : J} (S : Prefix F q0 factor j)
    (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    IsColimit (SmallObject.coconeOfLE (S.D ⋙ Arrow.leftFunc) hij) := by
  let Q := SmallObject.restrictionLT (S.D ⋙ Arrow.leftFunc) hij
  have hObj : (S.D.obj ⟨i, hij⟩).left = colimit Q :=
    congrArg Arrow.right (S.source_limit_eq i hi hij ⊥ hi.bot_lt)
  let e : colimit Q ≅ (S.D.obj ⟨i, hij⟩).left := (eqToIso hObj).symm
  refine IsColimit.ofIsoColimit (colimit.isColimit Q) (Cocone.ext e ?_)
  intro k
  have hk : k.1 < i := k.2
  let g : (⟨k.1, hk.le.trans hij⟩ : Set.Iic j) ⟶ ⟨i, hij⟩ := homOfLE hk.le
  have h := S.source_limit_eq i hi hij k.1 hk
  change colimit.ι Q k ≫ eqToHom hObj.symm = (S.D.map g).left
  exact map_eq_of_arrow_eq (S.D.map g).left (colimit.ι Q k) hObj h

end CategoryTheory.OriginalContinuousApproximation.Prefix
namespace CategoryTheory.OriginalContinuousApproximation.Prefix

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.SuccStruct

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  {F : J ⥤ C} {q0 : Arrow C} {P R : MorphismProperty C}
  {factor : MorphismProperty.FunctorialFactorizationData P R}

omit [WellFoundedLT J] in
/-- Every original limit of the next prefix is exactly an old source limit. -/
theorem successorDiagram_source_limit {j : J} (S : Prefix F q0 factor j) (hj : ¬IsMax j)
    (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ Order.succ j)
    (k : J) (hk : k < i) :
    Arrow.mk (((S.successorDiagram hj).map
      (homOfLE hk.le : ⟨k, hk.le.trans hij⟩ ⟶ ⟨i, hij⟩)).left) =
      Arrow.mk (colimit.ι (SmallObject.restrictionLT
        (S.successorDiagram hj ⋙ Arrow.leftFunc) hij) ⟨k, hk⟩) := by
  have hij' : i ≤ j := (Order.IsSuccLimit.le_succ_iff hi).mp hij
  have hRestrict := congrArg (fun D => D ⋙ Arrow.leftFunc) (S.successorDiagram_restrict hj)
  change SmallObject.restrictionLE (S.successorDiagram hj ⋙ Arrow.leftFunc)
    (Order.le_succ j) = S.D ⋙ Arrow.leftFunc at hRestrict
  change Arrow.mk ((SmallObject.restrictionLE (S.successorDiagram hj ⋙ Arrow.leftFunc)
    (Order.le_succ j)).map
      (homOfLE hk.le : ⟨k, hk.le.trans hij'⟩ ⟶ ⟨i, hij'⟩)) =
      Arrow.mk (colimit.ι (SmallObject.restrictionLT
        (SmallObject.restrictionLE (S.successorDiagram hj ⋙ Arrow.leftFunc)
          (Order.le_succ j)) hij') ⟨k, hk⟩)
  rw [hRestrict]
  exact S.source_limit_eq i hi hij' k hk

/-- The complete actual same-factory successor satisfies all canonical prefix clauses. -/
def successor {j : J} (S : Prefix F q0 factor j) (hj : ¬IsMax j) :
    Prefix F q0 factor (Order.succ j) where
  D := S.successorDiagram hj
  target_eq := S.successorDiagram_target hj
  bottom_eq := S.successorDiagram_bottom hj
  successor_eq := S.successorDiagram_successor_eq hj
  source_limit_eq := S.successorDiagram_source_limit hj

omit [WellFoundedLT J] in
/-- The whole constructed successor state keeps the exact original old prefix. -/
theorem successor_restrict {j : J} (S : Prefix F q0 factor j) (hj : ¬IsMax j) :
    (S.successor hj).restrict (Order.le_succ j) = S := by
  apply ext
  exact S.successorDiagram_restrict hj

end CategoryTheory.OriginalContinuousApproximation.Prefix

namespace CategoryTheory.OriginalContinuousApproximation

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.SuccStruct

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  (F : J ⥤ C) (q0 : Arrow C) {P R : MorphismProperty C}
  (factor : MorphismProperty.FunctorialFactorizationData P R)

namespace Limit

variable {F q0 factor} (m : J)
  (x : ((Set.principalSegIio m).monotone.functor.op ⋙ prefixFunctor F q0 factor).sections)

/-- The full actual original preceding Arrow diagram is glued from its complete prefix section. -/
def diagram : Set.Iio m ⥤ Arrow C := Glue.diagram (LowerSet.Iio m) x

omit [WellFoundedLT J] in
/-- The complete target projection is exactly the original restricted F on every stage map. -/
theorem diagram_target : diagram m x ⋙ Arrow.rightFunc =
    (Set.principalSegIio m).monotone.functor ⋙ F := by
  apply Functor.hext
  · intro i
    exact Functor.congr_obj (Glue.state (LowerSet.Iio m) x i).target_eq ⟨i.1, le_rfl⟩
  · intro i j f
    have hD := Glue.diagram_restrict (LowerSet.Iio m) x j
    have hR := congrArg (fun G => G ⋙ Arrow.rightFunc) hD
    have hTarget : (Glue.prefixInclusion (LowerSet.Iio m) j).monotone.functor ⋙
        (diagram m x ⋙ Arrow.rightFunc) =
      (Set.initialSegIic j.1).monotone.functor ⋙ F :=
      hR.trans (Glue.state (LowerSet.Iio m) x j).target_eq
    exact Functor.hcongr_hom hTarget
      (homOfLE (leOfHom f) : (⟨i.1, leOfHom f⟩ : Set.Iic j.1) ⟶ ⟨j.1, le_rfl⟩)

/-- The target limit cocone keeps the original F_m and every original F_k→F_m map. -/
def targetCocone : Cocone (diagram m x ⋙ Arrow.rightFunc) :=
  (Cocone.precompose (eqToHom (diagram_target m x))).obj
    ((Set.principalSegIio m).cocone F)

/-- The whole Arrow limit cocone has the real source colimit and exact original target F_m. -/
def cocone : Cocone (diagram m x) :=
  Comma.coconeOfPreserves (diagram m x) (colimit.isColimit (diagram m x ⋙ Arrow.leftFunc))
    (targetCocone m x)

/-- The complete actual limit prefix is the genuine extension of this Arrow cocone. -/
def extended : Set.Iic m ⥤ Arrow C := ofCocone (cocone m x)

end Limit

end CategoryTheory.OriginalContinuousApproximation

namespace CategoryTheory.OriginalContinuousApproximation.Limit

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.SuccStruct

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  {F : J ⥤ C} {q0 : Arrow C} {P R : MorphismProperty C}
  {factor : MorphismProperty.FunctorialFactorizationData P R}
  (m : J)
  (x : ((Set.principalSegIio m).monotone.functor.op ⋙ prefixFunctor F q0 factor).sections)

omit [WellFoundedLT J] in
/-- The complete actual limit prefix retains the original target diagram on every map. -/
theorem extended_target : extended m x ⋙ Arrow.rightFunc =
    (Set.initialSegIic m).monotone.functor ⋙ F := by
  rw [extended, ofCocone_comp]
  change ofCocone (targetCocone m x) = _
  exact (ofCocone_precompose_eq (diagram_target m x)
    ((Set.principalSegIio m).cocone F)).trans (ofCocone_original_eq F m)

omit [WellFoundedLT J] in
/-- The full actual source is precisely the preceding source diagram extended by its colimit. -/
theorem extended_source : extended m x ⋙ Arrow.leftFunc =
    ofCocone (colimit.cocone (diagram m x ⋙ Arrow.leftFunc)) := by
  rw [extended, ofCocone_comp]
  rfl

omit [WellFoundedLT J] in
/-- Every actual complete original old prefix remains literally unchanged at a new limit. -/
theorem extended_restrict (i : J) (hi : i < m) :
    SmallObject.restrictionLE (extended m x) hi.le =
      (x.val (Opposite.op (⟨i, hi⟩ : Set.Iio m))).D := by
  exact (ofCocone_restrict_eq (cocone m x) i hi).trans
    (Glue.diagram_restrict (LowerSet.Iio m) x ⟨i, hi⟩)

end CategoryTheory.OriginalContinuousApproximation.Limit
namespace CategoryTheory.OriginalContinuousApproximation.Limit

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.SuccStruct

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  {F : J ⥤ C} {q0 : Arrow C} {P R : MorphismProperty C}
  {factor : MorphismProperty.FunctorialFactorizationData P R}
  (m : J) (hm : Order.IsSuccLimit m)
  (x : ((Set.principalSegIio m).monotone.functor.op ⋙ prefixFunctor F q0 factor).sections)

omit [WellFoundedLT J] in
include hm in
/-- The real limit extension retains the original bottom Arrow without a changed endpoint. -/
theorem extended_bottom : (extended m x).obj ⟨⊥, bot_le⟩ = q0 :=
  (Functor.congr_obj (extended_restrict m x ⊥ hm.bot_lt)
    (⟨⊥, bot_le⟩ : Set.Iic (⊥ : J))).trans
    (x.val (Opposite.op (⟨⊥, hm.bot_lt⟩ : Set.Iio m))).bottom_eq

omit [WellFoundedLT J] in
include hm in
/-- Every complete original successor square at a new limit is inherited from its exact
larger canonical predecessor prefix. -/
theorem extended_successor (i : J) (hi : i < m) :
    Arrow.mk ((extended m x).map (homOfLE (Order.le_succ i) :
      ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩)) =
      Arrow.mk (successorSquare F factor i ((extended m x).obj ⟨i, hi.le⟩)
        (Functor.congr_obj (extended_target m x) ⟨i, hi.le⟩)) := by
  have hs : Order.succ i < m := (Order.IsSuccLimit.succ_lt_iff hm).mpr hi
  let S := x.val (Opposite.op (⟨Order.succ i, hs⟩ : Set.Iio m))
  have hR := extended_restrict m x (Order.succ i) hs
  have hMap := congrArg (fun D : Set.Iic (Order.succ i) ⥤ Arrow C =>
    Arrow.mk (D.map (homOfLE (Order.le_succ i) :
      (⟨i, Order.le_succ i⟩ : Set.Iic (Order.succ i)) ⟶ ⟨Order.succ i, le_rfl⟩))) hR
  change Arrow.mk ((extended m x).map (homOfLE (Order.le_succ i))) =
    Arrow.mk (S.D.map (homOfLE (Order.le_succ i))) at hMap
  have hlt : i < Order.succ i := Order.lt_succ_of_not_isMax (not_isMax_of_lt hi)
  calc
    _ = Arrow.mk (S.D.map (homOfLE (Order.le_succ i))) := hMap
    _ = Arrow.mk (successorSquare F factor i (S.D.obj ⟨i, hlt.le⟩)
        (Functor.congr_obj S.target_eq ⟨i, hlt.le⟩)) := S.successor_eq i hlt
    _ = _ := by
      have hObj := Functor.congr_obj hR (⟨i, hlt.le⟩ : Set.Iic (Order.succ i))
      exact successorSquare_eq F factor hObj.symm _ _

omit [WellFoundedLT J] in
/-- The true endpoint source at the limit is exactly the real colimit of its predecessors. -/
theorem extended_source_limit (i : J) (hi : Order.IsSuccLimit i) (him : i ≤ m)
    (k : J) (hk : k < i) :
    Arrow.mk (((extended m x).map (homOfLE hk.le :
      ⟨k, hk.le.trans him⟩ ⟶ ⟨i, him⟩)).left) =
      Arrow.mk (colimit.ι (SmallObject.restrictionLT
        (extended m x ⋙ Arrow.leftFunc) him) ⟨k, hk⟩) := by
  obtain him' | hEq := him.lt_or_eq
  · have hR := congrArg (fun D => D ⋙ Arrow.leftFunc) (extended_restrict m x i him')
    change SmallObject.restrictionLE (extended m x ⋙ Arrow.leftFunc) him'.le = _ at hR
    change Arrow.mk ((SmallObject.restrictionLE (extended m x ⋙ Arrow.leftFunc) him'.le).map
      (homOfLE hk.le : (⟨k, hk.le⟩ : Set.Iic i) ⟶ ⟨i, le_rfl⟩)) =
      Arrow.mk (colimit.ι (SmallObject.restrictionLT
        (SmallObject.restrictionLE (extended m x ⋙ Arrow.leftFunc) him'.le) le_rfl) ⟨k, hk⟩)
    rw [hR]
    exact (x.val (Opposite.op (⟨i, him'⟩ : Set.Iio m))).source_limit_eq i hi le_rfl k hk
  · subst i
    change Arrow.mk ((extended m x ⋙ Arrow.leftFunc).map (homOfLE hk.le :
      (⟨k, hk.le⟩ : Set.Iic m) ⟶ ⟨m, le_rfl⟩)) =
      Arrow.mk (colimit.ι (SmallObject.restrictionLT
        (extended m x ⋙ Arrow.leftFunc) le_rfl) ⟨k, hk⟩)
    rw [extended_source]
    have h := arrowMap_ofCocone_to_top (colimit.cocone (diagram m x ⋙ Arrow.leftFunc)) k hk
    change Arrow.mk ((ofCocone (colimit.cocone (diagram m x ⋙ Arrow.leftFunc))).map
      (homOfLE hk.le)) = _ at h
    rw [h]
    have hR := Functor.ext_of_iso
      (restrictionLTOfCoconeIso (colimit.cocone (diagram m x ⋙ Arrow.leftFunc)))
      (fun j => ofCocone_obj_eq _ j.1 j.2) (by intro j; rfl)
    rw [hR]
    rfl

/-- Actual original successor and preceding source colimits produce the full new canonical
limit state, with no desired weak or cofibrant conclusion as an input. -/
def state (hm : Order.IsSuccLimit m) : Prefix F q0 factor m where
  D := extended m x
  target_eq := extended_target m x
  bottom_eq := extended_bottom m hm x
  successor_eq := extended_successor m hm x
  source_limit_eq := extended_source_limit m x

omit [WellFoundedLT J] in
/-- The entire constructed limit state restricts to the same original compatible prefix. -/
theorem state_restrict (hm : Order.IsSuccLimit m) (i : J) (hi : i < m) :
    (state m x hm).restrict hi.le = x.val (Opposite.op (⟨i, hi⟩ : Set.Iio m)) := by
  apply Prefix.ext
  exact extended_restrict m x i hi

end CategoryTheory.OriginalContinuousApproximation.Limit

namespace CategoryTheory.OriginalContinuousApproximation

open CategoryTheory CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  (F : J ⥤ C) (q0 : Arrow C) {P R : MorphismProperty C}
  (factor : MorphismProperty.FunctorialFactorizationData P R)
  (hq0 : q0.right = F.obj ⊥)

/-- Actual canonical successor and source-colimit limit producers give the full
original inverse-system induction data. -/
def inductionData : (prefixFunctor F q0 factor).WellOrderInductionData where
  succ _j hj S := S.successor hj
  map_succ _j hj S := S.successor_restrict hj
  lift j hj x := Limit.state j x hj
  map_lift j hj x i hi := Limit.state_restrict j x hj i hi

/-- Every actual canonical prefix is constructed from the same original I bottom. -/
def fullSection : (prefixFunctor F q0 factor).sections :=
  (inductionData F q0 factor).sectionsMk (Prefix.bottom hq0)

/-- The complete original bottom prefix retains its actual original Q and counit Arrow. -/
theorem fullSection_bot : (fullSection F q0 factor hq0).val (Opposite.op ⊥) =
    Prefix.bottom hq0 :=
  (inductionData F q0 factor).sectionsMk_val_op_bot (Prefix.bottom hq0)

/-- The original full family is a complete actual Arrow diagram over the same J. -/
def fullDiagram : J ⥤ Arrow C :=
  let e : J →o ((⊤ : LowerSet J) : Set J) :=
    { toFun := fun j => ⟨j, by trivial⟩, monotone' := fun _ _ h => h }
  let x : ((OrderHom.Subtype.val
      (fun j : J => j ∈ ((⊤ : LowerSet J) : Set J))).monotone.functor.op ⋙
      prefixFunctor F q0 factor).sections :=
    { val := fun i => (fullSection F q0 factor hq0).val (Opposite.op i.unop.1)
      property := fun f => (fullSection F q0 factor hq0).property
        ((OrderHom.Subtype.val
          (fun j : J => j ∈ ((⊤ : LowerSet J) : Set J))).monotone.functor.map f.unop).op }
  e.monotone.functor ⋙ Glue.diagram (⊤ : LowerSet J) x

end CategoryTheory.OriginalContinuousApproximation
namespace CategoryTheory.OriginalContinuousApproximation

open CategoryTheory CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  (F : J ⥤ C) (q0 : Arrow C) {P R : MorphismProperty C}
  (factor : MorphismProperty.FunctorialFactorizationData P R)
  (hq0 : q0.right = F.obj ⊥)

/-- Every original full closed prefix is exactly the constructed canonical prefix. -/
theorem fullDiagram_restrict (j : J) :
    (Set.initialSegIic j).monotone.functor ⋙ fullDiagram F q0 factor hq0 =
      ((fullSection F q0 factor hq0).val (Opposite.op j)).D :=
  Glue.diagram_restrict (⊤ : LowerSet J) _ ⟨j, by trivial⟩

/-- Every original target object and map remains the caller's F. -/
theorem fullDiagram_target : fullDiagram F q0 factor hq0 ⋙ Arrow.rightFunc = F := by
  apply Functor.hext
  · intro i
    exact Functor.congr_obj ((fullSection F q0 factor hq0).val
      (Opposite.op i)).target_eq ⟨i, le_rfl⟩
  · intro i j f
    have hR := congrArg (fun D => D ⋙ Arrow.rightFunc)
      (fullDiagram_restrict F q0 factor hq0 j)
    have hTarget : (Set.initialSegIic j).monotone.functor ⋙
        (fullDiagram F q0 factor hq0 ⋙ Arrow.rightFunc) =
      (Set.initialSegIic j).monotone.functor ⋙ F :=
      hR.trans ((fullSection F q0 factor hq0).val (Opposite.op j)).target_eq
    exact Functor.hcongr_hom hTarget
      (homOfLE (leOfHom f) : (⟨i, leOfHom f⟩ : Set.Iic j) ⟶ ⟨j, le_rfl⟩)

/-- The original bottom source/counit Arrow is retained literally. -/
theorem fullDiagram_bottom : (fullDiagram F q0 factor hq0).obj ⊥ = q0 :=
  ((fullSection F q0 factor hq0).val (Opposite.op ⊥)).bottom_eq

/-- The full source approximation diagram retains every original ordinal transition. -/
def sourceDiagram : J ⥤ C := fullDiagram F q0 factor hq0 ⋙ Arrow.leftFunc

/-- The complete actual source counit retains every original F stage and map. -/
def sourceCounit : sourceDiagram F q0 factor hq0 ⟶ F :=
  Functor.whiskerLeft (fullDiagram F q0 factor hq0) Arrow.leftToRight ≫
    eqToHom (fullDiagram_target F q0 factor hq0)

end CategoryTheory.OriginalContinuousApproximation

namespace CategoryTheory.OriginalContinuousApproximation

open CategoryTheory CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  (F : J ⥤ C) (q0 : Arrow C) {P R : MorphismProperty C}
  (factor : MorphismProperty.FunctorialFactorizationData P R)
  (hq0 : q0.right = F.obj ⊥)

/-- Every genuine source limit keeps its actual original previous-stage colimit. -/
def sourceDiagramLimit (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit ((Set.principalSegIio m).cocone (sourceDiagram F q0 factor hq0)) := by
  let S := (fullSection F q0 factor hq0).val (Opposite.op m)
  have hR := congrArg (fun D => D ⋙ Arrow.leftFunc)
    (fullDiagram_restrict F q0 factor hq0 m)
  change (Set.initialSegIic m).monotone.functor ⋙ sourceDiagram F q0 factor hq0 =
    S.D ⋙ Arrow.leftFunc at hR
  have hC : IsColimit (SmallObject.coconeOfLE
      ((Set.initialSegIic m).monotone.functor ⋙ sourceDiagram F q0 factor hq0) le_rfl) := by
    rw [hR]
    exact S.sourceIsColimit m hm le_rfl
  exact hC

/-- The full constructed original source approximation is genuinely continuous for all F. -/
theorem sourceDiagram_continuous : (sourceDiagram F q0 factor hq0).IsWellOrderContinuous :=
  { nonempty_isColimit m hm := ⟨sourceDiagramLimit F q0 factor hq0 m hm⟩ }

end CategoryTheory.OriginalContinuousApproximation

namespace CategoryTheory.OriginalContinuousApproximation

open CategoryTheory CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  (F : J ⥤ C) (q0 : Arrow C) {P R : MorphismProperty C}
  (factor : MorphismProperty.FunctorialFactorizationData P R)
  (hq0 : q0.right = F.obj ⊥)

/-- Every full original successor Arrow square is the same exact original factory square. -/
theorem fullDiagram_successor (j : J) (hj : ¬IsMax j) :
    Arrow.mk ((fullDiagram F q0 factor hq0).map (homOfLE (Order.le_succ j))) =
      Arrow.mk (successorSquare F factor j ((fullDiagram F q0 factor hq0).obj j)
        (Functor.congr_obj (fullDiagram_target F q0 factor hq0) j)) := by
  let S := (fullSection F q0 factor hq0).val (Opposite.op (Order.succ j))
  have hR := fullDiagram_restrict F q0 factor hq0 (Order.succ j)
  have hMap := congrArg (fun D : Set.Iic (Order.succ j) ⥤ Arrow C =>
    Arrow.mk (D.map (homOfLE (Order.le_succ j) :
      (⟨j, Order.le_succ j⟩ : Set.Iic (Order.succ j)) ⟶ ⟨Order.succ j, le_rfl⟩))) hR
  change Arrow.mk ((fullDiagram F q0 factor hq0).map (homOfLE (Order.le_succ j))) =
    Arrow.mk (S.D.map (homOfLE (Order.le_succ j))) at hMap
  calc
    _ = Arrow.mk (S.D.map (homOfLE (Order.le_succ j))) := hMap
    _ = Arrow.mk (successorSquare F factor j (S.D.obj ⟨j, Order.le_succ j⟩)
        (Functor.congr_obj S.target_eq ⟨j, Order.le_succ j⟩)) :=
      S.successor_eq j (Order.lt_succ_of_not_isMax hj)
    _ = _ := successorSquare_eq F factor
      (Functor.congr_obj hR (⟨j, Order.le_succ j⟩ : Set.Iic (Order.succ j))).symm _ _

/-- Every source successor belongs to the actual original factory's left class. -/
theorem sourceDiagram_successor_mem (j : J) (hj : ¬IsMax j) :
    P ((sourceDiagram F q0 factor hq0).map (homOfLE (Order.le_succ j))) := by
  have h := congrArg (Functor.mapArrow Arrow.leftFunc).obj
    (fullDiagram_successor F q0 factor hq0 j hj)
  change Arrow.mk ((sourceDiagram F q0 factor hq0).map (homOfLE (Order.le_succ j))) =
    Arrow.mk (factor.i.app (Arrow.mk
      (((fullDiagram F q0 factor hq0).obj j).hom ≫
        eqToHom (Functor.congr_obj (fullDiagram_target F q0 factor hq0) j) ≫
          F.map (homOfLE (Order.le_succ j))))) at h
  rw [← P.arrow_mk_mem_toSet_iff, h, P.arrow_mk_mem_toSet_iff]
  exact factor.hi _

end CategoryTheory.OriginalContinuousApproximation

namespace CategoryTheory.OriginalContinuousApproximation

open CategoryTheory CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  (F : J ⥤ C) (q0 : Arrow C) {P R : MorphismProperty C}
  (factor : MorphismProperty.FunctorialFactorizationData P R)
  (hq0 : q0.right = F.obj ⊥)

/-- The complete original counit component retains the actual constructed Arrow and full
target equality, without replacing its map by an independently chosen resolution. -/
theorem sourceCounit_app (j : J) :
    (sourceCounit F q0 factor hq0).app j =
      ((fullDiagram F q0 factor hq0).obj j).hom ≫
        eqToHom (Functor.congr_obj (fullDiagram_target F q0 factor hq0) j) := by
  let D := fullDiagram F q0 factor hq0
  let h := fullDiagram_target F q0 factor hq0
  change (Functor.whiskerLeft D Arrow.leftToRight ≫ eqToHom h).app j = _
  exact congrArg (fun g => ((D.obj j).hom) ≫ g) (CategoryTheory.eqToHom_app h j)

end CategoryTheory.OriginalContinuousApproximation

namespace CategoryTheory.OriginalContinuousApproximation

open CategoryTheory CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  (F : J ⥤ C) (q0 : Arrow C) {P R : MorphismProperty C}
  (factor : MorphismProperty.FunctorialFactorizationData P R)
  (hq0 : q0.right = F.obj ⊥)

/-- The successor object's complete counit Arrow is the actual original right factor,
with the whole target equality preserved. -/
theorem sourceCounit_successor_mem (j : J) (hj : ¬IsMax j) :
    R ((sourceCounit F q0 factor hq0).app (Order.succ j)) := by
  have h := congrArg Arrow.right (fullDiagram_successor F q0 factor hq0 j hj)
  change (fullDiagram F q0 factor hq0).obj (Order.succ j) =
    Arrow.mk (factor.p.app (Arrow.mk
      (((fullDiagram F q0 factor hq0).obj j).hom ≫
        eqToHom (Functor.congr_obj (fullDiagram_target F q0 factor hq0) j) ≫
          F.map (homOfLE (Order.le_succ j))))) at h
  have hArrow : Arrow.mk ((sourceCounit F q0 factor hq0).app (Order.succ j)) =
      (fullDiagram F q0 factor hq0).obj (Order.succ j) := by
    rw [sourceCounit_app]
    exact Arrow.arrow_mk_comp_eqToHom _ _
  rw [← R.arrow_mk_mem_toSet_iff, hArrow, h, R.arrow_mk_mem_toSet_iff]
  exact factor.hp _

end CategoryTheory.OriginalContinuousApproximation
