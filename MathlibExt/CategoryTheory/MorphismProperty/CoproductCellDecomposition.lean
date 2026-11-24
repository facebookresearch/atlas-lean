/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.Order.SuccPred.Basic

/-! # Original coproduct arrows and their coordinate cell chains

Each coordinate switches along its original arrow exactly once. The actual
coproduct diagram is continuous, each genuine cell is an original pushout,
and its final arrow is the original `Sigma.map`. Isomorphism cells retain the
dummy bottom and the empty-family cases. No model or closure assumption enters.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty.CoproductCells

variable {C : Type u} [Category.{v} C]

/-- The original coordinate is its source before the switch and target afterwards. -/
def coordinateObj {ι K : Type w} [LinearOrder K]
    (A B : ι → C) (idx : ι → K) (i : ι) (s : K) : C :=
  if idx i < s then B i else A i

/-- A coordinate transition is the original arrow across its unique switch. -/
def coordinateMap {ι K : Type w} [LinearOrder K] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (idx : ι → K) {s t : K} (hst : s ≤ t) (i : ι) :
    coordinateObj A B idx i s ⟶ coordinateObj A B idx i t := by
  by_cases hs : idx i < s
  · have ht : idx i < t := hs.trans_le hst
    exact eqToHom (ite_eq_left hs) ≫ eqToHom (ite_eq_left ht).symm
  · by_cases ht : idx i < t
    · exact eqToHom (ite_eq_right hs) ≫ f i ≫ eqToHom (ite_eq_left ht).symm
    · exact eqToHom (ite_eq_right hs) ≫ eqToHom (ite_eq_right ht).symm

/-- Every original coordinate identity is literally the identity transition. -/
theorem coordinateMap_id {ι K : Type w} [LinearOrder K] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (idx : ι → K) (s : K) (i : ι) :
    coordinateMap f idx (show s ≤ s from le_rfl) i = 𝟙 _ := by
  by_cases hs : idx i < s <;> simp [coordinateMap, coordinateObj, hs]

/-- Coordinate transitions compose along the original ordered indices. -/
theorem coordinateMap_comp {ι K : Type w} [LinearOrder K] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (idx : ι → K) {r s t : K}
    (hrs : r ≤ s) (hst : s ≤ t) (i : ι) :
    coordinateMap f idx (hrs.trans hst) i =
      coordinateMap f idx hrs i ≫ coordinateMap f idx hst i := by
  by_cases hr : idx i < r
  · have hs : idx i < s := hr.trans_le hrs
    have ht : idx i < t := hs.trans_le hst
    simp [coordinateMap, coordinateObj, hr, hs, ht]
  · by_cases hs : idx i < s
    · have ht : idx i < t := hs.trans_le hst
      simp [coordinateMap, coordinateObj, hr, hs, ht]
    · by_cases ht : idx i < t
      · simp [coordinateMap, coordinateObj, hr, hs, ht]
      · simp [coordinateMap, coordinateObj, hr, hs, ht]

/-- The complete original family of coordinate transitions is a functor. -/
def coordinateDiagram {ι K : Type w} [LinearOrder K] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (idx : ι → K) : K ⥤ Discrete ι ⥤ C where
  obj s := Discrete.functor (fun i => coordinateObj A B idx i s)
  map hst :=
    { app := fun i => coordinateMap f idx (leOfHom hst) i.as
      naturality := by
        rintro ⟨a⟩ ⟨b⟩ g
        obtain rfl : a = b := Discrete.eq_of_hom g
        simp }
  map_id s := by
    ext ⟨i⟩
    exact coordinateMap_id f idx s i
  map_comp hst htu := by
    ext ⟨i⟩
    exact coordinateMap_comp f idx (leOfHom hst) (leOfHom htu) i

/-- Each object of the family diagram is the same original conditional coordinate. -/
theorem coordinateDiagram_obj {ι K : Type w} [LinearOrder K] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (idx : ι → K) (s : K) (i : ι) :
    ((coordinateDiagram f idx).obj s).obj ⟨i⟩ = coordinateObj A B idx i s := rfl

/-- Every diagram component is the original coordinate transition. -/
theorem coordinateDiagram_map {ι K : Type w} [LinearOrder K] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (idx : ι → K) {s t : K} (h : s ⟶ t) (i : ι) :
    ((coordinateDiagram f idx).map h).app ⟨i⟩ =
      coordinateMap f idx (leOfHom h) i := rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem coordinateMap_isIso_after {ι K : Type w} [LinearOrder K]
    {A B : ι → C} (f : ∀ i, A i ⟶ B i) (idx : ι → K)
    {s t : K} (hst : s ≤ t) (i : ι) (hi : idx i < s) :
    IsIso (coordinateMap f idx hst i) := by
  have ht : idx i < t := hi.trans_le hst
  refine ⟨⟨eqToHom (by simp [coordinateObj, hi, ht]), ?_, ?_⟩⟩ <;>
    simp [coordinateMap, coordinateObj, hi, ht, eqToHom_trans, eqToHom_refl]

set_option backward.isDefEq.respectTransparency.types false in
private theorem coordinateMap_isIso_before {ι K : Type w} [LinearOrder K]
    {A B : ι → C} (f : ∀ i, A i ⟶ B i) (idx : ι → K)
    {s t : K} (hst : s ≤ t) (i : ι) (hi : ¬idx i < t) :
    IsIso (coordinateMap f idx hst i) := by
  have hs : ¬idx i < s := fun h => hi (h.trans_le hst)
  refine ⟨⟨eqToHom (by simp [coordinateObj, hs, hi]), ?_, ?_⟩⟩ <;>
    simp [coordinateMap, coordinateObj, hs, hi, eqToHom_trans, eqToHom_refl]

private def coordinateFunctor {ι K : Type w} [LinearOrder K] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (idx : ι → K) (i : ι) : K ⥤ C :=
  coordinateDiagram f idx ⋙ (evaluation (Discrete ι) C).obj ⟨i⟩

private theorem coordinateFunctor_continuous {ι K : Type w}
    [LinearOrder K] [SuccOrder K] [OrderBot K]
    {A B : ι → C} (f : ∀ i, A i ⟶ B i) (idx : ι → K) (i : ι) :
    (coordinateFunctor f idx i).IsWellOrderContinuous := by
  constructor
  intro m hm
  let D := (Set.principalSegIio m).monotone.functor ⋙ coordinateFunctor f idx i
  let c := (Set.principalSegIio m).cocone (coordinateFunctor f idx i)
  by_cases hi : idx i < m
  · have hiMax : ¬IsMax (idx i) := not_isMax_iff.mpr ⟨m, hi⟩
    let i₀ : Set.Iio m := ⟨Order.succ (idx i), hm.succ_lt_iff.mpr hi⟩
    have hconst : D.IsEventuallyConstantFrom i₀ := by
      intro j g
      change IsIso (coordinateMap f idx (leOfHom g) i)
      exact coordinateMap_isIso_after f idx (leOfHom g) i
        (Order.lt_succ_of_not_isMax hiMax)
    let _ : IsIso (c.ι.app i₀) := by
      change IsIso (coordinateMap f idx i₀.2.le i)
      exact coordinateMap_isIso_after f idx i₀.2.le i
        (Order.lt_succ_of_not_isMax hiMax)
    let _ : Nonempty (Set.Iio m) := ⟨i₀⟩
    exact ⟨hconst.isColimitOfIsIso c⟩
  · have hmBot : (⊥ : K) < m := by
      simpa [bot_lt_iff_ne_bot] using hm.not_isMin
    let i₀ : Set.Iio m := ⟨⊥, hmBot⟩
    have hconst : D.IsEventuallyConstantFrom i₀ := by
      intro j g
      change IsIso (coordinateMap f idx (leOfHom g) i)
      exact coordinateMap_isIso_before f idx (leOfHom g) i
        (fun h => hi (h.trans j.2))
    let _ : IsIso (c.ι.app i₀) := by
      change IsIso (coordinateMap f idx i₀.2.le i)
      exact coordinateMap_isIso_before f idx i₀.2.le i hi
    let _ : Nonempty (Set.Iio m) := ⟨i₀⟩
    exact ⟨hconst.isColimitOfIsIso c⟩

/-- Every actual proper-limit cocone of the original family is a colimit. -/
theorem coordinateDiagram_continuous {ι K : Type w}
    [LinearOrder K] [SuccOrder K] [OrderBot K]
    {A B : ι → C} (f : ∀ i, A i ⟶ B i) (idx : ι → K) :
    (coordinateDiagram f idx).IsWellOrderContinuous := by
  constructor
  intro m hm
  refine ⟨evaluationJointlyReflectsColimits _ fun i => ?_⟩
  let _ : (coordinateFunctor f idx i.as).IsWellOrderContinuous :=
    coordinateFunctor_continuous f idx i.as
  exact (coordinateFunctor f idx i.as).isColimitOfIsWellOrderContinuous m hm

/-- The actual chosen coproduct of the original coordinate diagram. -/
def coproductDiagram {ι K : Type w} [LinearOrder K]
    [HasColimitsOfShape (Discrete ι) C] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (idx : ι → K) : K ⥤ C :=
  coordinateDiagram f idx ⋙ colim

/-- The same original coproduct diagram preserves its proper-limit cocones. -/
theorem coproductDiagram_continuous {ι K : Type w}
    [LinearOrder K] [SuccOrder K] [OrderBot K]
    [HasColimitsOfShape (Discrete ι) C] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (idx : ι → K) :
    (coproductDiagram f idx).IsWellOrderContinuous := by
  let _ : (coordinateDiagram f idx).IsWellOrderContinuous :=
    coordinateDiagram_continuous f idx
  let _ : PreservesWellOrderContinuousOfShape K
      (colim : (Discrete ι ⥤ C) ⥤ C) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  change (coordinateDiagram f idx ⋙ colim).IsWellOrderContinuous
  infer_instance

/-- A coproduct with only one nonisomorphism coordinate is its original pushout. -/
theorem sigmaMap_isPushout_of_isIso {ι : Type w}
    [HasColimitsOfShape (Discrete ι) C] {X Y : ι → C}
    (p : ∀ i, X i ⟶ Y i) (i : ι) (hp : ∀ j, j ≠ i → IsIso (p j)) :
    IsPushout (p i) (Sigma.ι X i) (Sigma.ι Y i) (Limits.Sigma.map p) := by
  classical
  have ht : IsColimit
      (PushoutCocone.mk (Sigma.ι Y i) (Limits.Sigma.map p)
        (Sigma.ι_map p i).symm) := by
    apply PushoutCocone.isColimitAux'
    intro s
    change { l : (∐ Y) ⟶ s.pt //
      Sigma.ι Y i ≫ l = s.inl ∧ Limits.Sigma.map p ≫ l = s.inr ∧
      ∀ {m : (∐ Y) ⟶ s.pt}, Sigma.ι Y i ≫ m = s.inl →
        Limits.Sigma.map p ≫ m = s.inr → m = l }
    let q : ∀ j, Y j ⟶ s.pt := fun j =>
      if hj : j = i then eqToHom (congrArg Y hj) ≫ s.inl
      else by
        let _ : IsIso (p j) := hp j hj
        exact inv (p j) ≫ Sigma.ι X j ≫ s.inr
    let l : (∐ Y) ⟶ s.pt := Sigma.desc q
    have hl₁ : Sigma.ι Y i ≫ l = s.inl := by
      dsimp [l]
      rw [Sigma.ι_comp_desc]
      simp [q]
    have hl₂ : Limits.Sigma.map p ≫ l = s.inr := by
      apply Sigma.hom_ext
      intro j
      dsimp [l]
      rw [← Category.assoc, Sigma.ι_map, Category.assoc, Sigma.ι_comp_desc]
      by_cases hj : j = i
      · subst hj
        simpa [q] using s.condition
      · let _ : IsIso (p j) := hp j hj
        simp [q, hj]
    refine ⟨l, hl₁, hl₂, ?_⟩
    intro m hm₁ hm₂
    apply Sigma.hom_ext
    intro j
    by_cases hj : j = i
    · subst hj
      rw [hl₁]
      exact hm₁
    · let _ : IsIso (p j) := hp j hj
      apply (cancel_epi (p j)).1
      rw [← Sigma.ι_map_assoc, hm₂, ← Sigma.ι_map_assoc, hl₂]
  exact IsPushout.of_isColimit ht

/-- The actual cell order includes its dummy bottom and final top. -/
abbrev cellOrder (ι : Type w) : Type w := WithTop (WithBot ι)

/-- An original label retains its position in the actual cell order. -/
def cellIndex {ι : Type w} (i : ι) : cellOrder ι :=
  ((i : WithBot ι) : WithTop (WithBot ι))

section Cells

variable {ι : Type w} [LinearOrder ι] {A B : ι → C} (f : ∀ i, A i ⟶ B i)

/-- The original family switches along the actual original cell order. -/
def cellDiagram [HasColimitsOfShape (Discrete ι) C] : cellOrder ι ⥤ C :=
  coproductDiagram f cellIndex

/-- The changed coordinate at its original stage is its original source. -/
def cellSourceIso (i : ι) :
    ((coordinateDiagram f cellIndex).obj (cellIndex i)).obj ⟨i⟩ ≅ A i :=
  eqToIso (ite_eq_right (lt_irrefl (cellIndex i)))

variable [SuccOrder (cellOrder ι)]

/-- The changed coordinate immediately after its stage is its original target. -/
def cellTargetIso (i : ι) :
    ((coordinateDiagram f cellIndex).obj (Order.succ (cellIndex i))).obj ⟨i⟩ ≅ B i :=
  eqToIso (ite_eq_left (Order.lt_succ_of_not_isMax (by simp [cellIndex, cellOrder])))

/-- The original changed source enters its coordinate coproduct through its actual iso. -/
def cellSourceInjection [HasColimitsOfShape (Discrete ι) C] (i : ι) :
    A i ⟶ (cellDiagram f).obj (cellIndex i) :=
  (cellSourceIso f i).inv ≫
    Sigma.ι (fun j => coordinateObj A B cellIndex j (cellIndex i)) i

/-- The original changed target enters the next coordinate coproduct through its actual iso. -/
def cellTargetInjection [HasColimitsOfShape (Discrete ι) C] (i : ι) :
    B i ⟶ (cellDiagram f).obj (Order.succ (cellIndex i)) :=
  (cellTargetIso f i).inv ≫
    Sigma.ι (fun j => coordinateObj A B cellIndex j (Order.succ (cellIndex i))) i

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every true cell is a pushout of the original arrow with both original cofan legs. -/
theorem cell_isPushout [HasColimitsOfShape (Discrete ι) C] (i : ι) :
    IsPushout (f i) (cellSourceInjection f i) (cellTargetInjection f i)
      ((cellDiagram f).map (homOfLE (Order.le_succ (cellIndex i)))) := by
  let p := fun j => coordinateMap f cellIndex (Order.le_succ (cellIndex i)) j
  have hp (j : ι) (hji : j ≠ i) : IsIso (p j) := by
    have hidx : cellIndex j ≠ cellIndex i := by
      simpa [cellIndex, cellOrder] using hji
    obtain hj | hj := lt_or_gt_of_ne hidx
    · exact coordinateMap_isIso_after f cellIndex (Order.le_succ _) j hj
    · exact coordinateMap_isIso_before f cellIndex (Order.le_succ _) j
        (not_lt_of_ge (Order.succ_le_of_lt hj))
  have sq := sigmaMap_isPushout_of_isIso p i hp
  apply sq.of_iso' (cellSourceIso f i).symm (cellTargetIso f i).symm
    (Iso.refl _) (Iso.refl _)
  · have hlt : cellIndex i < Order.succ (cellIndex i) :=
      Order.lt_succ_of_not_isMax (by simp [cellIndex, cellOrder])
    have hpi : p i = (cellSourceIso f i).hom ≫ f i ≫ (cellTargetIso f i).inv := by
      dsimp [p, cellSourceIso, cellTargetIso, eqToIso]
      simp only [coordinateMap, dite_eq_right (lt_irrefl (cellIndex i)), dite_eq_left hlt]
      rfl
    rw [hpi]
    exact Iso.inv_hom_id_assoc (cellSourceIso f i) _
  · dsimp only [Iso.symm_hom, Iso.refl_hom, cellSourceInjection]
    rw [Category.comp_id]
    rfl
  · dsimp only [Iso.symm_hom, Iso.refl_hom, cellTargetInjection]
    rw [Category.comp_id]
    rfl
  · dsimp only [Iso.refl_hom]
    rw [Category.id_comp, Category.comp_id]
    rfl

variable [WellFoundedLT ι] [HasColimitsOfShape (Discrete ι) C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original coproduct arrow has its actual complete coordinate cell witness. -/
def coproductMapOriginalCells :
    (isomorphisms C ⊔ (MorphismProperty.ofHoms f).pushouts).TransfiniteCompositionOfShape
      (cellOrder ι) (Limits.Sigma.map f) := by
  let F := cellDiagram f
  let hbot (i : ι) : coordinateObj A B cellIndex i ⊥ = A i := by
    dsimp only [coordinateObj]
    rw [ite_eq_right (not_lt_of_ge bot_le)]
  let htop (i : ι) : coordinateObj A B cellIndex i ⊤ = B i := by
    dsimp only [coordinateObj]
    rw [ite_eq_left (by simp [cellIndex, cellOrder])]
  let botNatIso : (coordinateDiagram f cellIndex).obj ⊥ ≅ Discrete.functor A :=
    NatIso.ofComponents (fun i => eqToIso (hbot i.as))
      (by
        intro X Y g
        have hXY : X = Y := Discrete.ext (Discrete.eq_of_hom g)
        subst Y
        have hg : g = 𝟙 X := Subsingleton.elim _ _
        subst g
        simp [coordinateDiagram])
  let topNatIso : (coordinateDiagram f cellIndex).obj ⊤ ≅ Discrete.functor B :=
    NatIso.ofComponents (fun i => eqToIso (htop i.as))
      (by
        intro X Y g
        have hXY : X = Y := Discrete.ext (Discrete.eq_of_hom g)
        subst Y
        have hg : g = 𝟙 X := Subsingleton.elim _ _
        subst g
        simp [coordinateDiagram])
  have hcomponent (i : ι) :
      botNatIso.inv.app ⟨i⟩ ≫
          ((coordinateDiagram f cellIndex).map
            (homOfLE (bot_le : (⊥ : cellOrder ι) ≤ ⊤))).app ⟨i⟩ ≫
          topNatIso.hom.app ⟨i⟩ = f i := by
    change (botNatIso.app ⟨i⟩).inv ≫
      ((coordinateDiagram f cellIndex).map
        (homOfLE (bot_le : (⊥ : cellOrder ι) ≤ ⊤))).app ⟨i⟩ ≫
      (topNatIso.app ⟨i⟩).hom = f i
    rw [show botNatIso.app ⟨i⟩ = eqToIso (hbot i) by
      dsimp [botNatIso]
      apply NatIso.ofComponents.app]
    rw [show topNatIso.app ⟨i⟩ = eqToIso (htop i) by
      dsimp [topNatIso]
      apply NatIso.ofComponents.app]
    dsimp only [coordinateDiagram, coordinateMap]
    have hs : ¬cellIndex i < (⊥ : cellOrder ι) := not_lt_of_ge bot_le
    have ht : cellIndex i < (⊤ : cellOrder ι) := by simp [cellIndex, cellOrder]
    rw [dite_eq_right hs, dite_eq_left ht]
    dsimp only [eqToIso]
    simp [coordinateObj, cellIndex, cellOrder, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  let botIso : F.obj ⊥ ≅ ∐ A := (colim : (Discrete ι ⥤ C) ⥤ C).mapIso botNatIso
  let topIso : F.obj ⊤ ≅ ∐ B := (colim : (Discrete ι ⥤ C) ⥤ C).mapIso topNatIso
  let incl : F ⟶ (Functor.const (cellOrder ι)).obj (∐ B) :=
    { app := fun s => F.map (homOfLE le_top) ≫ topIso.hom
      naturality := by
        intro s t g
        dsimp
        rw [Category.comp_id, ← Category.assoc, ← F.map_comp,
          Subsingleton.elim (g ≫ homOfLE le_top) (homOfLE le_top)] }
  let _ : F.IsWellOrderContinuous := coproductDiagram_continuous f cellIndex
  refine
    { F := F
      isoBot := botIso
      incl := incl
      isColimit := IsColimit.ofIsoColimit
        (colimitOfDiagramTerminal isTerminalTop F) (Cocone.ext topIso)
      fac := ?_
      map_mem := ?_ }
  · apply Sigma.hom_ext
    intro i
    dsimp [F, incl, botIso, topIso, cellDiagram, coproductDiagram]
    simp only [Sigma.ι_map]
    rw [← hcomponent i]
    simp [Category.assoc]
  · intro s hs
    induction s using WithTop.recTopCoe with
    | top => exact (hs isMax_top).elim
    | coe b =>
        induction b using WithBot.recBotCoe with
        | bot =>
            left
            let p := fun j => coordinateMap f cellIndex
              (Order.le_succ (((⊥ : WithBot ι) : cellOrder ι))) j
            change IsIso (Limits.Sigma.map p)
            let _ (j : ι) : IsIso (p j) := by
              have hlt : (((⊥ : WithBot ι) : cellOrder ι)) < cellIndex j :=
                WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe j)
              have ht : ¬cellIndex j <
                  Order.succ (((⊥ : WithBot ι) : cellOrder ι)) :=
                not_lt_of_ge (Order.succ_le_of_lt hlt)
              exact coordinateMap_isIso_before f cellIndex (Order.le_succ _) j ht
            infer_instance
        | coe i =>
            right
            exact (MorphismProperty.ofHoms f).pushouts_mk
              (cell_isPushout f i).flip (MorphismProperty.ofHoms.mk i)

/-- The witness uses exactly the original coordinate coproduct diagram. -/
theorem coproductMapOriginalCells_diagram :
    (coproductMapOriginalCells f).F = cellDiagram f := rfl

/-- The original initial and final maps compose to the original whole coproduct arrow. -/
theorem coproductMapOriginalCells_fac :
    (coproductMapOriginalCells f).isoBot.inv ≫
      (coproductMapOriginalCells f).incl.app ⊥ = Limits.Sigma.map f :=
  (coproductMapOriginalCells f).fac

/-- The same original final inclusion cocone has its actual universal property. -/
def coproductMapOriginalCellsIsColimit :
    IsColimit (Cocone.mk (∐ B) (coproductMapOriginalCells f).incl) :=
  (coproductMapOriginalCells f).isColimit

/-- Every original coproduct map is a cell composite of original pushouts and isomorphisms. -/
theorem coproductMap_originalCells :
    Nonempty
      ((isomorphisms C ⊔ (MorphismProperty.ofHoms f).pushouts).TransfiniteCompositionOfShape
        (cellOrder ι) (Limits.Sigma.map f)) :=
  ⟨coproductMapOriginalCells f⟩

end Cells

end CategoryTheory.MorphismProperty.CoproductCells
