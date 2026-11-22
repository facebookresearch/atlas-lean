/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CellularSource
public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Successors
import all MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Successors
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Adjoining one original cell to an actual closed prefix
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe w u v uD

open CategoryTheory Limits MorphismProperty Opposite
open CategoryTheory.SmallObject.SuccStruct
open HomotopicalAlgebra.CellularSubcomplexExtension

namespace HomotopicalAlgebra.CellularPrefixAdjoin

universe uT uI uK uP

private theorem transportedCellIndex_apply
    {T : Type uT} {I : T → Type uI} {K : Type uK}
    {P : (t : T) → (I t ↪ K) → Sort uP} {t s : T} (e : t = s)
    (z : Σ' f : I s ↪ K, P s f) (k : K) (hk : ∀ q, z.1 q = k) (q : I t) :
    (Eq.mpr (congrArg (fun t => Σ' f : I t ↪ K, P t f) e) z).1 q = k := by
  cases e
  exact hk q

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- An actual singleton cofan has its original object as colimit point. -/
def pointCofan (A : C) : Cofan (fun _ : PUnit.{w + 1} => A) :=
  Cofan.mk A (fun _ => 𝟙 A)

/-- The singleton cofan uses its original injection and actual universal property. -/
def pointCofanIsColimit (A : C) : IsColimit (pointCofan.{w} A) :=
  Cofan.IsColimit.mk _ (fun s => s.inj PUnit.unit)
    (fun s i => by
      obtain rfl : i = PUnit.unit := Subsingleton.elim _ _
      exact Category.id_comp _)
    (fun s m hm => (Category.id_comp m).symm.trans (hm PUnit.unit))

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (j : O) (hj : ¬ IsMax j)
  (v : CellularSubcomplex (prefixComplex d c j))
  (k : (c.attachCells j hj).ι)
  (a : ((c.attachCells j hj).π k).1.left ⟶ v.endpoint)
  (ha : a ≫ v.inclusion = boundary d c j hj k)

/-- The unchanged original generating arrow of the newly adjoined occurrence. -/
abbrev label : d.I.toSet := (c.attachCells j hj).π k

/-- The new endpoint is the actual stated pushout of the original attaching map and generator. -/
abbrev cellObject : C := pushout a (d.I.homFamily (label d c j hj k))

/-- The original prefix terminal cocone identifies its actual last stage with its actual endpoint. -/
def prefixEndpointIso : v.complex.F.obj (⟨j, le_rfl⟩ : Set.Iic j) ≅ v.endpoint := by
  let _ : IsIso (v.complex.incl.app (⟨j, le_rfl⟩ : Set.Iic j)) :=
    v.complex.isColimit.isIso_ι_app_of_isTerminal (⟨j, le_rfl⟩ : Set.Iic j) isTerminalTop
  exact asIso (v.complex.incl.app (⟨j, le_rfl⟩ : Set.Iic j))

/-- The genuine newly adjoined one-cell attachment has the exact stated pushout endpoint. -/
def oneAttach : AttachCells.{w} d.I.homFamily
    (pushout.inl a (d.I.homFamily (label d c j hj k))) where
  ι := PUnit
  π _ := label d c j hj k
  cofan₁ := pointCofan ((label d c j hj k).1.left)
  cofan₂ := pointCofan ((label d c j hj k).1.right)
  isColimit₁ := pointCofanIsColimit _
  isColimit₂ := pointCofanIsColimit _
  m := d.I.homFamily (label d c j hj k)
  hm _ := by simp [pointCofan]
  g₁ := a
  g₂ := pushout.inr a (d.I.homFamily (label d c j hj k))
  isPushout := IsPushout.of_hasPushout _ _

/-- The original last prefix stage enters the actual new pushout by its original endpoint map. -/
def nextMap : v.complex.F.obj (⟨j, le_rfl⟩ : Set.Iic j) ⟶ cellObject d c j hj v k a :=
  (prefixEndpointIso d c j v).hom ≫ pushout.inl a (d.I.homFamily (label d c j hj k))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The source transport uses only the original prefix terminal-cocone isomorphism. -/
def nextAttach : AttachCells.{w} d.I.homFamily (nextMap d c j hj v k a) :=
  (oneAttach d c j hj v k a).ofArrowIso
    (Arrow.isoMk (prefixEndpointIso d c j v).symm (Iso.refl _) (by
      change (prefixEndpointIso d c j v).inv ≫
        ((prefixEndpointIso d c j v).hom ≫ pushout.inl a (d.I.homFamily (label d c j hj k))) =
          pushout.inl a (d.I.homFamily (label d c j hj k)) ≫ 𝟙 _
      simp))

/-- The new original cell attaches to the same actual original ambient successor. -/
def nextComparison : cellObject d c j hj v k a ⟶ c.F.obj (Order.succ j) :=
  pushout.desc
    (v.inclusion ≫ c.F.map (homOfLE (Order.le_succ j)))
    ((c.attachCells j hj).cell k) (by
      rw [← Category.assoc, ha]
      exact boundary_cell d c j hj k)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original new root square retains the actual prefix and actual ambient successor maps. -/
theorem nextMap_comparison : nextMap d c j hj v k a ≫ nextComparison d c j hj v k a ha =
    v.comparison.app (⟨j, le_rfl⟩ : Set.Iic j) ≫ c.F.map (homOfLE (Order.le_succ j)) := by
  have hv : v.complex.incl.app (⟨j, le_rfl⟩ : Set.Iic j) ≫ v.inclusion =
      v.comparison.app (⟨j, le_rfl⟩ : Set.Iic j) := by
    have hv₀ := v.comparison_endpoint (⟨j, le_rfl⟩ : Set.Iic j)
    change v.complex.incl.app (⟨j, le_rfl⟩ : Set.Iic j) ≫ v.inclusion =
      v.comparison.app (⟨j, le_rfl⟩ : Set.Iic j) ≫ c.F.map (homOfLE (le_rfl : j ≤ j)) at hv₀
    have hid : c.F.map (homOfLE (le_rfl : j ≤ j)) = 𝟙 (c.F.obj j) := c.F.map_id j
    exact hv₀.trans
      ((congrArg (fun z => v.comparison.app (⟨j, le_rfl⟩ : Set.Iic j) ≫ z) hid).trans
        (Category.comp_id _))
  dsimp only [nextMap, nextComparison, prefixEndpointIso]
  change (v.complex.incl.app (⟨j, le_rfl⟩ : Set.Iic j) ≫
    pushout.inl a (d.I.homFamily (label d c j hj k))) ≫
      pushout.desc (v.inclusion ≫ c.F.map (homOfLE (Order.le_succ j)))
        ((c.attachCells j hj).cell k) _ = _
  rw [Category.assoc, pushout.inl_desc, ← Category.assoc, hv]

/-- The actual original prefix comparison is its corresponding Arrow-valued diagram. -/
def prefixArrows : Set.Iic j ⥤ Arrow C where
  obj i := Arrow.mk (v.comparison.app i)
  map u := Arrow.homMk (v.complex.F.map u) ((prefixComplex d c j).F.map u)
    (v.comparison.naturality u)
  map_id i := by
    ext
    · exact v.complex.F.map_id i
    · exact (prefixComplex d c j).F.map_id i
  map_comp u u' := by
    ext
    · exact v.complex.F.map_comp u u'
    · exact (prefixComplex d c j).F.map_comp u u'

/-- The new arrow of the exact original root-comparison square. -/
def nextArrow : (prefixArrows d c j v).obj (⟨j, le_rfl⟩ : Set.Iic j) ⟶
    Arrow.mk (nextComparison d c j hj v k a ha) :=
  Arrow.homMk (nextMap d c j hj v k a) (c.F.map (homOfLE (Order.le_succ j)))
    (nextMap_comparison d c j hj v k a ha)

/-- The new closed prefix retains the actual previous prefix diagram and new successor. -/
def F : Set.Iic (Order.succ j) ⥤ C := extendToSucc hj v.complex.F (nextMap d c j hj v k a)

/-- The original comparisons extend on the same closed prefix. -/
def extendedArrows : Set.Iic (Order.succ j) ⥤ Arrow C :=
  extendToSucc hj (prefixArrows d c j v) (nextArrow d c j hj v k a ha)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Projection preserves the exact actual extended source diagram. -/
theorem extendedArrows_left : extendedArrows d c j hj v k a ha ⋙ Arrow.leftFunc = F d c j hj v k a := by
  rw [extendedArrows, CategoryTheory.SmallObject.SuccStruct.extendToSucc_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Projection preserves the exact original ambient closed-prefix diagram. -/
theorem extendedArrows_right :
    extendedArrows d c j hj v k a ha ⋙ Arrow.rightFunc = (prefixComplex d c (Order.succ j)).F := by
  rw [extendedArrows, CategoryTheory.SmallObject.SuccStruct.extendToSucc_comp]
  change extendToSucc hj ((Set.initialSegIic j).monotone.functor ⋙ c.F)
    (c.F.map (homOfLE (Order.le_succ j))) = _
  exact CategoryTheory.SmallObject.SuccStruct.extendToSucc_original_eq hj c.F

/-- Every extended arrow retains its own actual source-to-target morphism. -/
def arrowHom : extendedArrows d c j hj v k a ha ⋙ Arrow.leftFunc ⟶
    extendedArrows d c j hj v k a ha ⋙ Arrow.rightFunc where
  app i := ((extendedArrows d c j hj v k a ha).obj i).hom
  naturality _ _ u := ((extendedArrows d c j hj v k a ha).map u).w

/-- The actual whole comparison to the original ambient closed prefix. -/
def comparison : F d c j hj v k a ⟶ (prefixComplex d c (Order.succ j)).F :=
  eqToHom (extendedArrows_left d c j hj v k a ha).symm ≫
    arrowHom d c j hj v k a ha ≫ eqToHom (extendedArrows_right d c j hj v k a ha)

/-- The actual extended source preserves all genuine original prefix limit cocones. -/
theorem wellOrderContinuous : (F d c j hj v k a).IsWellOrderContinuous :=
  CellularPlateau.extendToSuccContinuous hj v.complex.F (nextMap d c j hj v k a)

/-- The original actual new endpoint is the terminal point of the new closed prefix. -/
def endpointIso : (F d c j hj v k a).obj (⊤ : Set.Iic (Order.succ j)) ≅ cellObject d c j hj v k a :=
  extendToSuccObjSuccIso hj v.complex.F (nextMap d c j hj v k a)

/-- The original root isomorphism is retained at the same original bottom stage. -/
def botIso : (F d c j hj v k a).obj ⊥ ≅ X :=
  extendToSuccObjIso hj v.complex.F (nextMap d c j hj v k a) ⊥ bot_le ≪≫ v.complex.isoBot

/-- Every original stage enters the actual new endpoint via the original extended transition. -/
def endpointCocone : Cocone (F d c j hj v k a) :=
  (coconeOfDiagramTerminal isTerminalTop (F d c j hj v k a)).extend (endpointIso d c j hj v k a).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual new endpoint cocone is colimiting by its actual terminal prefix stage. -/
def endpointIsColimit : IsColimit (endpointCocone d c j hj v k a) :=
  IsColimit.ofIsoColimit (colimitOfDiagramTerminal isTerminalTop (F d c j hj v k a))
    (Cocone.ext (endpointIso d c j hj v k a))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Each unchanged original prefix stage has its same original endpoint map followed by the new root. -/
theorem endpointCocone_old (i : O) (hi : i ≤ j) :
    (endpointCocone d c j hj v k a).ι.app ⟨i, hi.trans (Order.le_succ j)⟩ =
      (extendToSuccObjIso hj v.complex.F (nextMap d c j hj v k a) i hi).hom ≫
        v.complex.incl.app ⟨i, hi⟩ ≫ pushout.inl a (d.I.homFamily (label d c j hj k)) := by
  dsimp only [endpointCocone]
  change (F d c j hj v k a).map (homOfLE le_top) ≫ (endpointIso d c j hj v k a).hom = _
  have hcomp : (homOfLE le_top : (⟨i, hi.trans (Order.le_succ j)⟩ : Set.Iic (Order.succ j)) ⟶ ⊤) =
      (homOfLE hi : (⟨i, hi.trans (Order.le_succ j)⟩ : Set.Iic (Order.succ j)) ⟶ ⟨j, Order.le_succ j⟩) ≫
        (homOfLE (Order.le_succ j) : (⟨j, Order.le_succ j⟩ : Set.Iic (Order.succ j)) ⟶ ⊤) := Subsingleton.elim _ _
  rw [hcomp, (F d c j hj v k a).map_comp]
  dsimp only [F, endpointIso]
  rw [extendToSucc_map_le_succ]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, extendToSuccObjIso_hom_naturality]
  dsimp only [nextMap, prefixEndpointIso]
  change ((extendToSuccObjIso hj v.complex.F (nextMap d c j hj v k a) i hi).hom ≫
    v.complex.F.map (homOfLE hi)) ≫
      (v.complex.incl.app ⟨j, le_rfl⟩ ≫ pushout.inl a (d.I.homFamily (label d c j hj k))) = _
  simp only [Category.assoc]
  rw [← Category.assoc (v.complex.F.map (homOfLE hi)),
    (Cocone.mk v.endpoint v.complex.incl).w]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unchanged original root factors through exactly this new endpoint cocone. -/
theorem root_fac : (botIso d c j hj v k a).inv ≫ (endpointCocone d c j hj v k a).ι.app ⊥ =
    v.hom ≫ pushout.inl a (d.I.homFamily (label d c j hj k)) := by
  change (botIso d c j hj v k a).inv ≫
    (endpointCocone d c j hj v k a).ι.app ⟨⊥, bot_le⟩ = _
  rw [endpointCocone_old d c j hj v k a ⊥ bot_le]
  dsimp only [botIso]
  simp only [Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]
  change v.complex.isoBot.inv ≫
    (v.complex.incl.app (⊥ : Set.Iic j) ≫ pushout.inl a (d.I.homFamily (label d c j hj k))) = _
  rw [← Category.assoc]
  exact congrArg (fun z => z ≫ pushout.inl a (d.I.homFamily (label d c j hj k))) v.complex.fac

omit v a ha [OrderBot O] [WellFoundedLT O] in
/-- The original coefficient successor of an old stage remains inside the original prefix. -/
theorem oldSucc_le (i : Set.Iic (Order.succ j)) (hi : i.1 < j) : Order.succ i.1 ≤ j :=
  Order.succ_le_of_lt hi

/-- The same old stage viewed inside the original closed prefix. -/
abbrev oldIndex (i : Set.Iic (Order.succ j)) (hi : i.1 < j) : Set.Iic j := ⟨i.1, hi.le⟩

omit v a ha [OrderBot O] [WellFoundedLT O] in
/-- Every old attaching stage is genuinely nonmaximal in the old prefix. -/
theorem oldNotMax (i : Set.Iic (Order.succ j)) (hi : i.1 < j) : ¬ IsMax (oldIndex j i hi) :=
  not_isMax_iff.mpr ⟨⊤, hi⟩

/-- The original source isomorphism at an unchanged old stage. -/
def oldSourceIso (i : Set.Iic (Order.succ j)) (hi : i.1 < j) :
    (F d c j hj v k a).obj i ≅ v.complex.F.obj (oldIndex j i hi) :=
  extendToSuccObjIso hj v.complex.F (nextMap d c j hj v k a) i.1 hi.le

/-- The original target isomorphism at an unchanged old successor. -/
def oldTargetIso (i : Set.Iic (Order.succ j)) (hiMax : ¬ IsMax i) (hi : i.1 < j) :
    (F d c j hj v k a).obj (Order.succ i) ≅ v.complex.F.obj (Order.succ (oldIndex j i hi)) :=
  extendToSuccObjIso hj v.complex.F (nextMap d c j hj v k a)
    (Order.succ i).1 (by rw [prefixSuccessorEq i hiMax]; exact oldSucc_le j i hi) ≪≫
      v.complex.F.mapIso (eqToIso (Subtype.ext
        ((prefixSuccessorEq i hiMax).trans (Set.Iic.coe_succ_of_not_isMax (oldNotMax j i hi)).symm)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unchanged old successor arrow retains exactly its two original comparison isomorphisms. -/
theorem oldStep_naturality (i : Set.Iic (Order.succ j)) (hiMax : ¬ IsMax i) (hi : i.1 < j) :
    (F d c j hj v k a).map (homOfLE (Order.le_succ i)) ≫
        (oldTargetIso d c j hj v k a i hiMax hi).hom =
      (oldSourceIso d c j hj v k a i hi).hom ≫
        v.complex.F.map (homOfLE (Order.le_succ (oldIndex j i hi))) := by
  dsimp only [oldTargetIso, oldSourceIso, Iso.trans_hom, F]
  rw [← Category.assoc, extendToSuccObjIso_hom_naturality]
  simp only [Category.assoc]
  change (extendToSuccObjIso hj v.complex.F (nextMap d c j hj v k a) i.1 hi.le).hom ≫
    (v.complex.F.map
      (homOfLE (show (oldIndex j i hi) ≤
          (⟨(Order.succ i).1, by rw [prefixSuccessorEq i hiMax]; exact oldSucc_le j i hi⟩ : Set.Iic j) from
        (Order.le_succ i))) ≫ v.complex.F.map (eqToHom (Subtype.ext
          ((prefixSuccessorEq i hiMax).trans
            (Set.Iic.coe_succ_of_not_isMax (oldNotMax j i hi)).symm)))) = _
  rw [← v.complex.F.map_comp]
  congr 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An old cell attachment is transported only along its actual old source and successor isomorphisms. -/
def oldStepIso (i : Set.Iic (Order.succ j)) (hiMax : ¬ IsMax i) (hi : i.1 < j) :
    Arrow.mk (v.complex.F.map (homOfLE (Order.le_succ (oldIndex j i hi)))) ≅
      Arrow.mk ((F d c j hj v k a).map (homOfLE (Order.le_succ i))) :=
  Arrow.isoMk (oldSourceIso d c j hj v k a i hi).symm (oldTargetIso d c j hj v k a i hiMax hi).symm
    (by
      change (oldSourceIso d c j hj v k a i hi).inv ≫
          (F d c j hj v k a).map (homOfLE (Order.le_succ i)) =
        v.complex.F.map (homOfLE (Order.le_succ (oldIndex j i hi))) ≫
          (oldTargetIso d c j hj v k a i hiMax hi).inv
      apply (cancel_epi (oldSourceIso d c j hj v k a i hi).hom).1
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      apply (cancel_mono (oldTargetIso d c j hj v k a i hiMax hi).hom).1
      rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact oldStep_naturality d c j hj v k a i hiMax hi)

/-- The exact original new attaching stage in the extended closed prefix. -/
abbrev newStage : Set.Iic (Order.succ j) := ⟨j, Order.le_succ j⟩

omit d c v k a ha [OrderBot O] [WellFoundedLT O] in
include hj in
/-- The original new attaching stage is genuinely nonmaximal. -/
theorem newStageNotMax : ¬ IsMax (newStage j) :=
  not_isMax_iff.mpr ⟨⊤, Order.lt_succ_of_not_isMax hj⟩

omit d c v k a ha [OrderBot O] [WellFoundedLT O] in
include hj in
/-- Its actual closed-prefix successor is exactly the new terminal stage. -/
theorem newStageSuccessor : Order.succ (newStage j) = (⊤ : Set.Iic (Order.succ j)) :=
  Subtype.ext (prefixSuccessorEq (newStage j) (newStageNotMax j hj))

/-- The new attaching arrow has exactly its original source and actual pushout endpoint. -/
def newStepToTopIso : Arrow.mk (nextMap d c j hj v k a) ≅
    Arrow.mk ((F d c j hj v k a).map
      (homOfLE (Order.le_succ j) : newStage j ⟶ ⊤)) :=
  Arrow.isoMk
    (extendToSuccObjIso hj v.complex.F (nextMap d c j hj v k a) j le_rfl).symm
    (endpointIso d c j hj v k a).symm (by
      change (extendToSuccObjIso hj v.complex.F (nextMap d c j hj v k a) j le_rfl).inv ≫
        (F d c j hj v k a).map (homOfLE (Order.le_succ j) : newStage j ⟶ ⊤) =
          nextMap d c j hj v k a ≫ (endpointIso d c j hj v k a).inv
      dsimp only [F]
      rw [extendToSucc_map_le_succ]
      change (extendToSuccObjIso hj v.complex.F (nextMap d c j hj v k a) j le_rfl).inv ≫
        ((extendToSuccObjIso hj v.complex.F (nextMap d c j hj v k a) j le_rfl).hom ≫
          nextMap d c j hj v k a ≫ (endpointIso d c j hj v k a).inv) = _
      rw [Iso.inv_hom_id_assoc])

/-- A literal equality of original target stages transports only the original diagram target. -/
def targetStageIso {i x y : Set.Iic (Order.succ j)} (hix : i ≤ x) (hiy : i ≤ y) (e : x = y) :
    Arrow.mk ((F d c j hj v k a).map (homOfLE hix)) ≅
      Arrow.mk ((F d c j hj v k a).map (homOfLE hiy)) :=
  Arrow.isoMk (Iso.refl _) ((F d c j hj v k a).mapIso (eqToIso e)) (by
    change 𝟙 _ ≫ (F d c j hj v k a).map (homOfLE hiy) =
      (F d c j hj v k a).map (homOfLE hix) ≫ (F d c j hj v k a).map (eqToHom e)
    rw [Category.id_comp, ← (F d c j hj v k a).map_comp]
    congr 1)

/-- The exact successor equality gives the new attaching arrow in the extended closed-prefix history. -/
def newStepIso : Arrow.mk (nextMap d c j hj v k a) ≅
    Arrow.mk ((F d c j hj v k a).map (homOfLE (Order.le_succ (newStage j)))) :=
  (newStepToTopIso d c j hj v k a).trans
    (targetStageIso d c j hj v k a (Order.le_succ j) (Order.le_succ (newStage j))
      (newStageSuccessor j hj).symm)

/-- All old occurrences retain their original attachment; the one new original occurrence is added at j. -/
def attachCells (i : Set.Iic (Order.succ j)) (hiMax : ¬ IsMax i) :
    AttachCells.{w} d.I.homFamily ((F d c j hj v k a).map (homOfLE (Order.le_succ i))) := by
  have hij : i.1 ≤ j := (Order.lt_succ_iff_of_not_isMax hj).mp (prefixStage_lt_endpoint i hiMax)
  by_cases hi : i.1 < j
  · exact (v.complex.attachCells (oldIndex j i hi) (oldNotMax j i hi)).ofArrowIso
      (oldStepIso d c j hj v k a i hiMax hi)
  · have he : i.1 = j := le_antisymm hij (not_lt.mp hi)
    obtain rfl : i = newStage j := Subtype.ext he
    exact (nextAttach d c j hj v k a).ofArrowIso (newStepIso d c j hj v k a)

/-- This is the actual new closed-prefix I-cell history at the exact original root and pushout endpoint. -/
def complex : RelativeCellComplex.{w} (fun _ : Set.Iic (Order.succ j) => d.I.homFamily)
    (v.hom ≫ pushout.inl a (d.I.homFamily (label d c j hj k))) where
  F := F d c j hj v k a
  isoBot := botIso d c j hj v k a
  isWellOrderContinuous := wellOrderContinuous d c j hj v k a
  incl := (endpointCocone d c j hj v k a).ι
  isColimit := endpointIsColimit d c j hj v k a
  fac := root_fac d c j hj v k a
  attachCells := attachCells d c j hj v k a

end HomotopicalAlgebra.CellularPrefixAdjoin

namespace HomotopicalAlgebra.CellularPrefixAdjoin

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (j : O) (hj : ¬ IsMax j)
  (v : CellularSubcomplex (prefixComplex d c j))
  (k : (c.attachCells j hj).ι)
  (a : ((c.attachCells j hj).π k).1.left ⟶ v.endpoint)
  (ha : a ≫ v.inclusion = boundary d c j hj k)

omit [ModelCategory C] in
private theorem arrowHom_heq_of_eq {A B : Arrow C} (e : A = B) : A.hom ≍ B.hom := by
  cases e
  rfl

/-- Equality transports do not alter the actual extended Arrow component. -/
theorem comparison_app_heq (i : Set.Iic (Order.succ j)) :
    (comparison d c j hj v k a ha).app i ≍ ((extendedArrows d c j hj v k a ha).obj i).hom := by
  dsimp only [comparison]
  simp only [NatTrans.comp_app, eqToHom_app, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

/-- The extended comparison retains every original closed-prefix component. -/
theorem comparison_old (i : O) (hi : i ≤ j) :
    (comparison d c j hj v k a ha).app ⟨i, hi.trans (Order.le_succ j)⟩ =
      (extendToSuccObjIso hj v.complex.F (nextMap d c j hj v k a) i hi).hom ≫
        v.comparison.app ⟨i, hi⟩ := by
  apply eq_of_heq
  have he : (extendedArrows d c j hj v k a ha).obj ⟨i, hi.trans (Order.le_succ j)⟩ =
      (prefixArrows d c j v).obj ⟨i, hi⟩ :=
    extendToSucc_obj_eq hj (prefixArrows d c j v) (nextArrow d c j hj v k a ha) i hi
  have hs : (extendToSuccObjIso hj v.complex.F (nextMap d c j hj v k a) i hi).hom ≫
      v.comparison.app ⟨i, hi⟩ ≍ v.comparison.app ⟨i, hi⟩ := by
    dsimp only [extendToSuccObjIso,
      CategoryTheory.SmallObject.SuccStruct.extendToSucc.objIso, eqToIso.hom]
    exact eqToHom_comp_heq _ _
  exact (comparison_app_heq d c j hj v k a ha _).trans
    ((arrowHom_heq_of_eq he).trans hs.symm)

/-- The new comparison component is the actual original-cell pushout descender. -/
theorem comparison_top :
    (comparison d c j hj v k a ha).app (⊤ : Set.Iic (Order.succ j)) =
      (endpointIso d c j hj v k a).hom ≫ nextComparison d c j hj v k a ha := by
  apply eq_of_heq
  have he : (extendedArrows d c j hj v k a ha).obj (⊤ : Set.Iic (Order.succ j)) =
      Arrow.mk (nextComparison d c j hj v k a ha) :=
    extendToSucc_obj_succ_eq hj (prefixArrows d c j v) (nextArrow d c j hj v k a ha)
  have hs : (endpointIso d c j hj v k a).hom ≫ nextComparison d c j hj v k a ha ≍
      nextComparison d c j hj v k a ha := by
    dsimp only [endpointIso, extendToSuccObjSuccIso,
      CategoryTheory.SmallObject.SuccStruct.extendToSucc.objSuccIso, eqToIso.hom]
    exact eqToHom_comp_heq _ _
  exact (comparison_app_heq d c j hj v k a ha _).trans
    ((arrowHom_heq_of_eq he).trans hs.symm)

/-- The extended actual comparison keeps the original bottom equation. -/
theorem comparison_bot :
    (botIso d c j hj v k a).inv ≫ (comparison d c j hj v k a ha).app ⊥ =
      (prefixComplex d c (Order.succ j)).isoBot.inv := by
  change (botIso d c j hj v k a).inv ≫
    (comparison d c j hj v k a ha).app ⟨⊥, bot_le⟩ = _
  rw [comparison_old d c j hj v k a ha ⊥ bot_le]
  dsimp only [botIso, Iso.trans_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact v.comparison_bot

/-- Naturality at the actual terminal vertex gives every endpoint equation. -/
theorem comparison_endpoint (i : Set.Iic (Order.succ j)) :
    (endpointCocone d c j hj v k a).ι.app i ≫ nextComparison d c j hj v k a ha =
      (comparison d c j hj v k a ha).app i ≫
        (prefixComplex d c (Order.succ j)).incl.app i := by
  change ((F d c j hj v k a).map (homOfLE le_top) ≫ (endpointIso d c j hj v k a).hom) ≫
    nextComparison d c j hj v k a ha =
      (comparison d c j hj v k a ha).app i ≫
        (prefixComplex d c (Order.succ j)).F.map (homOfLE le_top)
  rw [Category.assoc, ← comparison_top d c j hj v k a ha]
  exact (comparison d c j hj v k a ha).naturality (homOfLE le_top)

/-- The exact occurrence embedding and its label equations are constructed together. -/
def extensionCellLabels (i : Set.Iic (Order.succ j)) (hiMax : ¬ IsMax i) :
    Σ' e : ((complex d c j hj v k a).attachCells i hiMax).ι ↪
        ((prefixComplex d c (Order.succ j)).attachCells i hiMax).ι,
      ∀ q : ((complex d c j hj v k a).attachCells i hiMax).ι,
        ((complex d c j hj v k a).attachCells i hiMax).π q =
          ((prefixComplex d c (Order.succ j)).attachCells i hiMax).π (e q) := by
  have hij : i.1 ≤ j := (Order.lt_succ_iff_of_not_isMax hj).mp (prefixStage_lt_endpoint i hiMax)
  by_cases hi : i.1 < j
  · have he : (complex d c j hj v k a).attachCells i hiMax =
        (v.complex.attachCells (oldIndex j i hi) (oldNotMax j i hi)).ofArrowIso
          (oldStepIso d c j hj v k a i hiMax hi) := by
      dsimp only [complex, attachCells]
      exact dite_eq_left hi
    rw [he]
    exact ⟨v.cellIndex (oldIndex j i hi) (oldNotMax j i hi),
      fun q => v.label_eq (oldIndex j i hi) (oldNotMax j i hi) q⟩
  · have he : i = newStage j := Subtype.ext (le_antisymm hij (not_lt.mp hi))
    subst i
    have he : (complex d c j hj v k a).attachCells (newStage j) hiMax =
        (nextAttach d c j hj v k a).ofArrowIso (newStepIso d c j hj v k a) := by
      dsimp only [complex, attachCells, newStage]
      exact dite_eq_right (lt_irrefl j)
    rw [he]
    refine ⟨?_, ?_⟩
    · change PUnit.{w + 1} ↪ (c.attachCells j hj).ι
      exact ⟨fun _ => k, fun x y _ => Subsingleton.elim x y⟩
    · intro q
      rfl

/-- The new history selects old original occurrences and the literal new occurrence at j. -/
def extensionCellIndex (i : Set.Iic (Order.succ j)) (hiMax : ¬ IsMax i) :
    ((complex d c j hj v k a).attachCells i hiMax).ι ↪
      ((prefixComplex d c (Order.succ j)).attachCells i hiMax).ι :=
  (extensionCellLabels d c j hj v k a i hiMax).1

/-- The extended occurrence selection retains each actual original generating arrow. -/
theorem extensionLabel_eq (i : Set.Iic (Order.succ j)) (hiMax : ¬ IsMax i)
    (q : ((complex d c j hj v k a).attachCells i hiMax).ι) :
    ((complex d c j hj v k a).attachCells i hiMax).π q =
      ((prefixComplex d c (Order.succ j)).attachCells i hiMax).π
        (extensionCellIndex d c j hj v k a i hiMax q) :=
  (extensionCellLabels d c j hj v k a i hiMax).2 q

section OldTargetIndices

variable {Q : Type w} [LinearOrder Q] [SuccOrder Q]
  (b : Q) (i : Set.Iic (Order.succ b)) (hiMax : ¬ IsMax i) (hi : i.1 < b)

/-- The original successor viewed in the unchanged old closed prefix. -/
def oldTargetIndex : Set.Iic b :=
  ⟨(Order.succ i).1, by rw [prefixSuccessorEq i hiMax]; exact Order.succ_le_of_lt hi⟩

/-- Both descriptions name the same literal original old successor. -/
theorem oldTargetEq : oldTargetIndex b i hiMax hi = Order.succ (oldIndex b i hi) :=
  Subtype.ext ((prefixSuccessorEq i hiMax).trans
    (Set.Iic.coe_succ_of_not_isMax (oldNotMax b i hi)).symm)

end OldTargetIndices

/-- Only equality of the original old successor transports the ambient target. -/
def ambientOldTargetIso (i : Set.Iic (Order.succ j)) (hiMax : ¬ IsMax i) (hi : i.1 < j) :
    (prefixComplex d c j).F.obj (Order.succ (oldIndex j i hi)) ≅
      (prefixComplex d c (Order.succ j)).F.obj (Order.succ i) :=
  (prefixComplex d c j).F.mapIso (eqToIso (oldTargetEq j i hiMax hi).symm)

/-- An old cell target comparison is transported by its exact original successor equality. -/
theorem oldTarget_comparison (i : Set.Iic (Order.succ j)) (hiMax : ¬ IsMax i) (hi : i.1 < j) :
    (oldTargetIso d c j hj v k a i hiMax hi).inv ≫
        (comparison d c j hj v k a ha).app (Order.succ i) =
      v.comparison.app (Order.succ (oldIndex j i hi)) ≫
        (ambientOldTargetIso d c j i hiMax hi).hom := by
  dsimp only [oldTargetIso, Iso.trans_inv]
  rw [comparison_old d c j hj v k a ha (Order.succ i).1
    (by rw [prefixSuccessorEq i hiMax]; exact oldSucc_le j i hi)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change v.complex.F.map (eqToHom (oldTargetEq j i hiMax hi).symm) ≫
      v.comparison.app (oldTargetIndex j i hiMax hi) =
    v.comparison.app (Order.succ (oldIndex j i hi)) ≫
      (prefixComplex d c j).F.map (eqToHom (oldTargetEq j i hiMax hi).symm)
  exact v.comparison.naturality (eqToHom (oldTargetEq j i hiMax hi).symm)

/-- The old original ambient cell map becomes the same new-prefix ambient cell map. -/
theorem ambientCell_old (i : Set.Iic (Order.succ j)) (hiMax : ¬ IsMax i) (hi : i.1 < j)
    (q : ((prefixComplex d c j).attachCells (oldIndex j i hi) (oldNotMax j i hi)).ι) :
    ((prefixComplex d c j).attachCells (oldIndex j i hi) (oldNotMax j i hi)).cell q ≫
        (ambientOldTargetIso d c j i hiMax hi).hom =
      ((prefixComplex d c (Order.succ j)).attachCells i hiMax).cell q := by
  rw [prefixComplex_cell d c j (oldIndex j i hi) (oldNotMax j i hi),
    prefixComplex_cell d c (Order.succ j) i hiMax, Category.assoc]
  dsimp only [ambientOldTargetIso, Functor.mapIso_hom, eqToIso.hom]
  simp only [eqToHom_map, eqToHom_trans]

omit [ModelCategory C] in
/-- An Arrow isomorphism transports a cell only by its original target component. -/
theorem ofArrowIso_cell {T : Type uD} {A B : T → C} {basic : ∀ x, A x ⟶ B x}
    {L R L' R' : C} {f : L ⟶ R} {f' : L' ⟶ R'}
    (z : AttachCells.{w} basic f) (e : Arrow.mk f ≅ Arrow.mk f') (q : z.ι) :
    (z.ofArrowIso e).cell q = z.cell q ≫ e.hom.right := by
  exact (Category.assoc _ _ _).symm

/-- The source transport of the singleton attachment keeps its literal original cell map. -/
theorem nextAttach_cell (q : (nextAttach d c j hj v k a).ι) :
    (nextAttach d c j hj v k a).cell q =
      pushout.inr a (d.I.homFamily (label d c j hj k)) := by
  change PUnit.{w + 1} at q
  cases q
  change 𝟙 _ ≫ (pushout.inr a (d.I.homFamily (label d c j hj k)) ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

/-- The literal new successor equality preserves its actual comparison map. -/
theorem newStep_comparison :
    (newStepIso d c j hj v k a).hom.right ≫
        (comparison d c j hj v k a ha).app (Order.succ (newStage j)) =
      nextComparison d c j hj v k a ha ≫
        (prefixComplex d c (Order.succ j)).F.map (eqToHom (newStageSuccessor j hj).symm) := by
  change ((endpointIso d c j hj v k a).inv ≫
      (F d c j hj v k a).map (eqToHom (newStageSuccessor j hj).symm)) ≫
        (comparison d c j hj v k a ha).app (Order.succ (newStage j)) = _
  rw [Category.assoc, (comparison d c j hj v k a ha).naturality
    (eqToHom (newStageSuccessor j hj).symm), ← Category.assoc,
    comparison_top d c j hj v k a ha]
  simp only [Iso.inv_hom_id_assoc]

/-- The original new cell map retains only its literal closed-prefix target transport. -/
theorem ambientCell_new (hiMax : ¬ IsMax (newStage j)) :
    ((prefixComplex d c (Order.succ j)).attachCells (newStage j) hiMax).cell k =
      (c.attachCells j hj).cell k ≫
        (prefixComplex d c (Order.succ j)).F.map (eqToHom (newStageSuccessor j hj).symm) := by
  rw [prefixComplex_cell d c (Order.succ j) (newStage j) hiMax]
  simp only [eqToHom_map]

/-- The occurrence selection, original labels and actual cell comparison equations are derived together. -/
def extensionCellData (i : Set.Iic (Order.succ j)) (hiMax : ¬ IsMax i) :
    Σ' e : ((complex d c j hj v k a).attachCells i hiMax).ι ↪
        ((prefixComplex d c (Order.succ j)).attachCells i hiMax).ι,
      Σ' hlabel : ∀ q : ((complex d c j hj v k a).attachCells i hiMax).ι,
        ((complex d c j hj v k a).attachCells i hiMax).π q =
          ((prefixComplex d c (Order.succ j)).attachCells i hiMax).π (e q),
      ∀ q : ((complex d c j hj v k a).attachCells i hiMax).ι,
        ((complex d c j hj v k a).attachCells i hiMax).cell q ≫
            (comparison d c j hj v k a ha).app (Order.succ i) =
          eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (hlabel q)) ≫
            ((prefixComplex d c (Order.succ j)).attachCells i hiMax).cell (e q) := by
  have hij : i.1 ≤ j := (Order.lt_succ_iff_of_not_isMax hj).mp (prefixStage_lt_endpoint i hiMax)
  by_cases hi : i.1 < j
  · have he : (complex d c j hj v k a).attachCells i hiMax =
        (v.complex.attachCells (oldIndex j i hi) (oldNotMax j i hi)).ofArrowIso
          (oldStepIso d c j hj v k a i hiMax hi) := by
      dsimp only [complex, attachCells]
      exact dite_eq_left hi
    rw [he]
    refine ⟨v.cellIndex (oldIndex j i hi) (oldNotMax j i hi),
      (fun q => v.label_eq (oldIndex j i hi) (oldNotMax j i hi) q), ?_⟩
    intro q
    rw [ofArrowIso_cell]
    change ((v.complex.attachCells (oldIndex j i hi) (oldNotMax j i hi)).cell q ≫
        (oldTargetIso d c j hj v k a i hiMax hi).inv) ≫
          (comparison d c j hj v k a ha).app (Order.succ i) = _
    rw [Category.assoc, oldTarget_comparison d c j hj v k a ha i hiMax hi,
      ← Category.assoc, v.cell_eq, Category.assoc, ambientCell_old]
    rfl
  · have he : i = newStage j := Subtype.ext (le_antisymm hij (not_lt.mp hi))
    subst i
    have he : (complex d c j hj v k a).attachCells (newStage j) hiMax =
        (nextAttach d c j hj v k a).ofArrowIso (newStepIso d c j hj v k a) := by
      dsimp only [complex, attachCells, newStage]
      exact dite_eq_right (lt_irrefl j)
    rw [he]
    refine ⟨?_, ?_, ?_⟩
    · change PUnit.{w + 1} ↪ (c.attachCells j hj).ι
      exact ⟨fun _ => k, fun x y _ => Subsingleton.elim x y⟩
    · intro q
      rfl
    · intro q
      simp only [eqToHom_refl, Category.id_comp]
      rw [ofArrowIso_cell, nextAttach_cell]
      rw [Category.assoc, newStep_comparison d c j hj v k a ha, ← Category.assoc]
      dsimp only [nextComparison]
      rw [pushout.inr_desc]
      exact (ambientCell_new d c j hj k hiMax).symm

/-- The actual one-cell extension is a genuine subcomplex of the unchanged next original prefix. -/
def subcomplex : CellularSubcomplex (prefixComplex d c (Order.succ j)) where
  endpoint := cellObject d c j hj v k a
  hom := v.hom ≫ pushout.inl a (d.I.homFamily (label d c j hj k))
  inclusion := nextComparison d c j hj v k a ha
  complex := complex d c j hj v k a
  comparison := comparison d c j hj v k a ha
  comparison_bot := comparison_bot d c j hj v k a ha
  comparison_endpoint := comparison_endpoint d c j hj v k a ha
  cellIndex i hiMax := (extensionCellData d c j hj v k a ha i hiMax).1
  label_eq i hiMax := (extensionCellData d c j hj v k a ha i hiMax).2.1
  cell_eq i hiMax := (extensionCellData d c j hj v k a ha i hiMax).2.2

section StageDecomposition

variable {Q : Type w} [LinearOrder Q] [SuccOrder Q] (b : Q) (hb : ¬ IsMax b)

/-- The extended original prefix has its old attaching stages and one new original attaching stage. -/
def stageEquiv : {i : Set.Iic (Order.succ b) // ¬ IsMax i} ≃
    {i : Set.Iic b // ¬ IsMax i} ⊕ PUnit.{w + 1} where
  toFun x := if hi : x.1.1 < b then
    Sum.inl ⟨oldIndex b x.1 hi, oldNotMax b x.1 hi⟩ else Sum.inr PUnit.unit
  invFun x := match x with
    | Sum.inl x => ⟨⟨x.1.1, x.1.2.trans (Order.le_succ b)⟩,
        not_isMax_iff.mpr ⟨⊤, (prefixStage_lt_endpoint x.1 x.2).trans_le (Order.le_succ b)⟩⟩
    | Sum.inr _ => ⟨newStage b, newStageNotMax b hb⟩
  left_inv x := by
    by_cases hi : x.1.1 < b
    · simp only [dite_eq_left hi]
    · have hx : x.1.1 ≤ b :=
        (Order.lt_succ_iff_of_not_isMax hb).mp (prefixStage_lt_endpoint x.1 x.2)
      have he : x.1.1 = b := le_antisymm hx (not_lt.mp hi)
      simp only [dite_eq_right hi]
      apply Subtype.ext
      apply Subtype.ext
      exact he.symm
  right_inv x := by
    cases x with
    | inl x =>
      have hi := prefixStage_lt_endpoint x.1 x.2
      simp only [dite_eq_left hi]
    | inr x =>
      cases x
      simp only [dite_eq_right (lt_irrefl b)]

end StageDecomposition

omit [ModelCategory C] in
/-- The actual original cells are their actual nonmaximal stage and original occurrence index. -/
def cellStageEquiv {Q : Type w} [LinearOrder Q] [OrderBot Q] [SuccOrder Q] [WellFoundedLT Q]
    {P : MorphismProperty C} {L R : C} {f : L ⟶ R}
    (z : RelativeCellComplex.{w} (fun _ : Q => P.homFamily) f) :
    z.Cells ≃ Σ i : {i : Q // ¬ IsMax i}, (z.attachCells i.1 i.2).ι where
  toFun x := ⟨⟨x.j, x.hj⟩, x.k⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual one-cell extension has exactly the old occurrence count plus one. -/
theorem cells_cardinal : Cardinal.mk (complex d c j hj v k a).Cells =
    Cardinal.mk v.complex.Cells + 1 := by
  let N := {i : Set.Iic (Order.succ j) // ¬ IsMax i}
  let M := {i : Set.Iic j // ¬ IsMax i}
  let G : M ⊕ PUnit.{w + 1} → Type w := fun z => match z with
    | Sum.inl z => (v.complex.attachCells z.1 z.2).ι
    | Sum.inr _ => PUnit.{w + 1}
  have hcount : Cardinal.mk (Σ i : N, ((complex d c j hj v k a).attachCells i.1 i.2).ι) =
      Cardinal.mk (Σ i : M ⊕ PUnit.{w + 1}, G i) := by
    apply Cardinal.mk_sigma_congr (stageEquiv j hj)
    intro i
    by_cases hi : i.1.1 < j
    · change Cardinal.mk ((complex d c j hj v k a).attachCells i.1 i.2).ι =
        Cardinal.mk (G (if hi : i.1.1 < j then
          Sum.inl ⟨oldIndex j i.1 hi, oldNotMax j i.1 hi⟩ else Sum.inr PUnit.unit))
      rw [dite_eq_left hi]
      dsimp only [G, complex, attachCells]
      rw [dite_eq_left hi]
      rfl
    · have hij : i.1.1 ≤ j :=
        (Order.lt_succ_iff_of_not_isMax hj).mp (prefixStage_lt_endpoint i.1 i.2)
      have he : i = ⟨newStage j, newStageNotMax j hj⟩ :=
        Subtype.ext (Subtype.ext (le_antisymm hij (not_lt.mp hi)))
      subst i
      change Cardinal.mk ((complex d c j hj v k a).attachCells (newStage j)
          (newStageNotMax j hj)).ι = Cardinal.mk (G (if hi : j < j then
          Sum.inl ⟨oldIndex j (newStage j) hi, oldNotMax j (newStage j) hi⟩ else Sum.inr PUnit.unit))
      rw [dite_eq_right (lt_irrefl j)]
      dsimp only [G, complex, attachCells, newStage]
      rw [dite_eq_right (lt_irrefl j)]
      rfl
  calc
    Cardinal.mk (complex d c j hj v k a).Cells =
        Cardinal.mk (Σ i : N, ((complex d c j hj v k a).attachCells i.1 i.2).ι) :=
      Cardinal.mk_congr (cellStageEquiv (complex d c j hj v k a))
    _ = Cardinal.mk (Σ i : M ⊕ PUnit.{w + 1}, G i) := hcount
    _ = Cardinal.mk ((Σ i : M, G (Sum.inl i)) ⊕ (Σ i : PUnit.{w + 1}, G (Sum.inr i))) :=
      Cardinal.mk_congr (Equiv.sumSigmaDistrib G)
    _ = Cardinal.mk v.complex.Cells + 1 := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id,
        ← Cardinal.mk_congr (cellStageEquiv v.complex)]
      simp only [G, Cardinal.mk_sigma, Cardinal.sum_const', Cardinal.mk_punit, mul_one]

/-- The bounded extension returns to the exact original full O, retaining its actual endpoint. -/
def fullSubcomplex : CellularSubcomplex c :=
  CellularPlateau.subcomplex d c (Order.succ j) (subcomplex d c j hj v k a ha)

/-- Plateau introduces no original cell; the full unchanged original O has the exact same count. -/
theorem fullSubcomplex_cells : Cardinal.mk (fullSubcomplex d c j hj v k a ha).complex.Cells =
    Cardinal.mk v.complex.Cells + 1 := by
  rw [fullSubcomplex, CellularPlateau.cells_cardinal]
  exact cells_cardinal d c j hj v k a

/-- Returning the singleton extension to the full original order retains
the literal newly adjoined occurrence in its actual original support. -/
theorem fullCell_mem_support :
    ({ j := j, hj := hj, k := k } : c.Cells) ∈ (fullSubcomplex d c j hj v k a ha).support := by
  let s := subcomplex d c j hj v k a ha
  let hj' := newStageNotMax j hj
  have hι : ((complex d c j hj v k a).attachCells (newStage j) hj').ι = PUnit.{w + 1} := by
    dsimp only [complex, attachCells, newStage]
    rw [dite_eq_right (lt_irrefl j)]
    rfl
  let q := (Equiv.cast hι).symm PUnit.unit
  let x : s.complex.Cells := { j := newStage j, hj := hj', k := q }
  have hsel : s.cellIndex (newStage j) hj' q = k := by
    let target := (prefixComplex d c (Order.succ j)).attachCells (newStage j) hj'
    let P (z : AttachCells.{w} d.I.homFamily
        ((complex d c j hj v k a).F.map (homOfLE (Order.le_succ (newStage j)))))
        (e : z.ι ↪ target.ι) :=
      Σ' hl : ∀ q, z.π q = target.π (e q),
        ∀ q, z.cell q ≫ (comparison d c j hj v k a ha).app (Order.succ (newStage j)) =
          eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (hl q)) ≫ target.cell (e q)
    have he : (complex d c j hj v k a).attachCells (newStage j) hj' =
        (nextAttach d c j hj v k a).ofArrowIso (newStepIso d c j hj v k a) := by
      dsimp only [complex, attachCells, newStage]
      exact dite_eq_right (lt_irrefl j)
    simp only [s, subcomplex, extensionCellData, newStage, lt_irrefl, dite_false]
    apply transportedCellIndex_apply (I := fun z => z.ι) (P := P) he
    intro q
    rfl
  rw [fullSubcomplex, CellularPlateau.support]
  refine ⟨s.originalCell x, ⟨x, rfl⟩, ?_⟩
  change ({ j := j, hj := hj, k := s.cellIndex (newStage j) hj' q } : c.Cells) = _
  exact congrArg (fun z => ({ j := j, hj := hj, k := z } : c.Cells)) hsel

/-- The literal new original cell has its original codomain map into the actual full endpoint. -/
def fullCellTarget : ((c.attachCells j hj).π k).1.right ⟶
    (fullSubcomplex d c j hj v k a ha).endpoint :=
  pushout.inr a (d.I.homFamily (label d c j hj k))

/-- The full original endpoint comparison recovers the literal original new cell inclusion. -/
theorem fullCellTarget_inclusion : fullCellTarget d c j hj v k a ha ≫
    (fullSubcomplex d c j hj v k a ha).inclusion =
      ({ j := j, hj := hj, k := k } : c.Cells).ι := by
  change pushout.inr a (d.I.homFamily (label d c j hj k)) ≫
    (nextComparison d c j hj v k a ha ≫ c.incl.app (Order.succ j)) =
      (c.attachCells j hj).cell k ≫ c.incl.app (Order.succ j)
  rw [← Category.assoc]
  dsimp only [nextComparison]
  rw [pushout.inr_desc]

/-- Adjoin the same original cell under the same original root, with only its derived boundary factor. -/
theorem exists_original_adjoin (e : c.Cells)
    (s : CellularSubcomplex (prefixComplex d c e.j))
    (h : e.i.1.left ⟶ s.endpoint)
    (hh : h ≫ s.inclusion = boundary d c e.j e.hj e.k) :
    ∃ t : CellularSubcomplex c,
      Cardinal.mk t.complex.Cells ≤ Cardinal.mk s.complex.Cells + 1 ∧
      ∃ g : e.i.1.right ⟶ t.endpoint, g ≫ t.inclusion = e.ι := by
  refine ⟨fullSubcomplex d c e.j e.hj s e.k h hh,
    (fullSubcomplex_cells d c e.j e.hj s e.k h hh).le,
    fullCellTarget d c e.j e.hj s e.k h hh, ?_⟩
  exact fullCellTarget_inclusion d c e.j e.hj s e.k h hh

end HomotopicalAlgebra.CellularPrefixAdjoin
