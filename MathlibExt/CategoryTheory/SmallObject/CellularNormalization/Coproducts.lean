/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.OriginalShapes
public import MathlibExt.CategoryTheory.MorphismProperty.CoproductCellDecomposition
public import MathlibExt.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Coproducts of original varying cellular histories

Use the existing original coordinate chain, its actual bottom transition,
original coordinate injections and only the stated per-injection pushouts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u v w κ ν

namespace CategoryTheory.SmallObject.CellularNormalization

section OriginalCoordinateHistories

variable {C : Type u} [Category.{v} C]
variable {ι : Type w} [LinearOrder ι] [WellFoundedLT ι]
variable [HasColimitsOfShape (Discrete ι) C]
variable {A B : ι → C} (f : ∀ i, A i ⟶ B i)
variable (K : ι → OriginalInnerShape.{κ})
variable (c : ∀ i, TransfiniteCompositionOfShape (K i).carrier (f i))

variable [∀ i, HasPushoutsAlong (MorphismProperty.CoproductCells.cellSourceInjection f i)]

/-- The original ordered coproduct coordinates, including the bottom and greatest stages. -/
abbrev coordinateOrder := MorphismProperty.CoproductCells.cellOrder ι

/-- The actual well-founded successor order on the original coproduct coordinate chain. -/
noncomputable local instance coordinateOrderSucc : SuccOrder (coordinateOrder (ι := ι)) :=
  SuccOrder.ofLinearWellFoundedLT _
/-- The original coordinate presentation of the actual whole coproduct map `Sigma.map f`. -/
noncomputable abbrev coordinatePresentation :=
  (MorphismProperty.CoproductCells.coproductMapOriginalCells f).toTransfiniteCompositionOfShape

/-- The actual inner shape of a coproduct coordinate switch comes from that original coordinate. -/
noncomputable def coordinateSwitchShape (s : {s : coordinateOrder (ι := ι) // ¬ IsMax s}) :
    OriginalInnerShape.{κ} := by
  classical
  rcases s with ⟨s, hs⟩
  induction s using WithTop.recTopCoe with
  | top => exact (hs isMax_top).elim
  | coe b =>
    induction b using WithBot.recBotCoe with
    | bot => exact
        { carrier := ULift.{κ} (Fin 1)
          linearOrder := inferInstance
          orderBot := inferInstance
          succOrder := SuccOrder.ofLinearWellFoundedLT (ULift.{κ} (Fin 1))
          wellFounded := inferInstance }
    | coe i => exact K i

omit [∀ i, HasPushoutsAlong (MorphismProperty.CoproductCells.cellSourceInjection f i)] in
/-- The actual coordinate-chain dummy-bottom transition is an isomorphism. -/
theorem coordinateBottom_isIso :
    IsIso ((coordinatePresentation f).F.map
        (homOfLE (Order.le_succ (⊥ : coordinateOrder (ι := ι))))) := by
  let p := fun i => MorphismProperty.CoproductCells.coordinateMap f
    MorphismProperty.CoproductCells.cellIndex (Order.le_succ (⊥ : coordinateOrder (ι := ι))) i
  change IsIso (Limits.Sigma.map p)
  let _ (i : ι) : IsIso (p i) := by
    have hlt : (⊥ : coordinateOrder (ι := ι)) < MorphismProperty.CoproductCells.cellIndex i := by
      exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe i)
    have hb : ¬ MorphismProperty.CoproductCells.cellIndex i < (⊥ : coordinateOrder (ι := ι)) :=
      not_lt_of_ge bot_le
    have hs : ¬ MorphismProperty.CoproductCells.cellIndex i <
        Order.succ (⊥ : coordinateOrder (ι := ι)) :=
      not_lt_of_ge (Order.succ_le_of_lt hlt)
    change IsIso (MorphismProperty.CoproductCells.coordinateMap f
      MorphismProperty.CoproductCells.cellIndex (Order.le_succ (⊥ : coordinateOrder (ι := ι))) i)
    let e₀ : MorphismProperty.CoproductCells.coordinateObj A B
        MorphismProperty.CoproductCells.cellIndex i (⊥ : coordinateOrder (ι := ι)) ≅ A i :=
      eqToIso (ite_eq_right hb)
    let e₁ : MorphismProperty.CoproductCells.coordinateObj A B
        MorphismProperty.CoproductCells.cellIndex i
            (Order.succ (⊥ : coordinateOrder (ι := ι))) ≅ A i :=
      eqToIso (ite_eq_right hs)
    have hmap : MorphismProperty.CoproductCells.coordinateMap f
        MorphismProperty.CoproductCells.cellIndex (Order.le_succ (⊥ : coordinateOrder (ι := ι))) i =
        e₀.hom ≫ e₁.inv := by
      unfold MorphismProperty.CoproductCells.coordinateMap
      rw [dite_eq_right hb, dite_eq_right hs]
      rfl
    exact hmap.symm ▸ (by infer_instance : IsIso (e₀.hom ≫ e₁.inv))
  infer_instance

/-- The original isomorphism at the dummy bottom has an actual one-stage history. -/
noncomputable def coordinateBottomHistory :
    TransfiniteCompositionOfShape (Fin 1)
      ((coordinatePresentation f).F.map (homOfLE
          (Order.le_succ (⊥ : coordinateOrder (ι := ι))))) := by
  let _ := coordinateBottom_isIso f
  let q := (coordinatePresentation f).F.map (homOfLE (Order.le_succ (⊥ : coordinateOrder (ι := ι))))
  let _ : IsIso q := coordinateBottom_isIso f
  let base := TransfiniteCompositionOfShape.ofComposableArrows
      (ComposableArrows.mk₀ ((coordinatePresentation f).F.obj ⊥))
  let eq : Arrow.mk (𝟙 ((coordinatePresentation f).F.obj ⊥)) ≅ Arrow.mk q :=
    Arrow.isoMk (Iso.refl _) (asIso q) (by simp)
  exact base.ofArrowIso eq

/-- The supplied coordinate history is pushed out through its original coordinate inclusion. -/
noncomputable def coordinateInnerHistory
    (i : ι) : TransfiniteCompositionOfShape (K i).carrier
      ((coordinatePresentation f).F.map (homOfLE
          (Order.le_succ (MorphismProperty.CoproductCells.cellIndex i)))) := by
  let P : MorphismProperty C := ⊤
  let original : P.TransfiniteCompositionOfShape (K i).carrier (f i) :=
    { toTransfiniteCompositionOfShape := c i
      map_mem k hk := trivial }
  exact (original.cobaseChange (MorphismProperty.CoproductCells.cellSourceInjection f i)
    (MorphismProperty.CoproductCells.cell_isPushout f i).flip).toTransfiniteCompositionOfShape

/-- Every original nonmaximal coordinate-chain stage has its own supplied or constructed inner
history. -/
noncomputable def coordinateSwitchHistory
    (s : {s : coordinateOrder (ι := ι) // ¬ IsMax s}) :
    TransfiniteCompositionOfShape (coordinateSwitchShape K s).carrier
      ((coordinatePresentation f).F.map (homOfLE (Order.le_succ s.1))) := by
  classical
  rcases s with ⟨s, hs⟩
  induction s using WithTop.recTopCoe with
  | top => exact (hs isMax_top).elim
  | coe b =>
    induction b using WithBot.recBotCoe with
    | bot =>
      let T := coordinateSwitchShape K ⟨(⊥ : coordinateOrder (ι := ι)), hs⟩
      let _ : LinearOrder T.carrier := T.linearOrder
      let _ : OrderBot T.carrier := T.orderBot
      let _ : SuccOrder T.carrier := T.succOrder
      let _ : WellFoundedLT T.carrier := T.wellFounded
      let E : T.carrier ≃o Fin 1 := { toEquiv := Equiv.ulift, map_rel_iff' := Iff.rfl }
      exact (coordinateBottomHistory f).ofOrderIso E
    | coe i => exact coordinateInnerHistory f K c i

/-- Actual cellular membership is preserved by the original coordinate pushout history. -/
theorem coordinateInnerHistory_mem (P : MorphismProperty C)
    [P.IsStableUnderCobaseChange]
    (hc : ∀ (i : ι) (k : (K i).carrier) (_ : ¬ IsMax k),
      P ((c i).F.map (homOfLE (Order.le_succ k))))
    (i : ι) (k : (K i).carrier) (hk : ¬ IsMax k) :
    P ((coordinateInnerHistory f K c i).F.map (homOfLE (Order.le_succ k))) := by
  let original : P.TransfiniteCompositionOfShape (K i).carrier (f i) :=
    { toTransfiniteCompositionOfShape := c i
      map_mem k hk := hc i k hk }
  let pushed := original.cobaseChange (MorphismProperty.CoproductCells.cellSourceInjection f i)
    (MorphismProperty.CoproductCells.cell_isPushout f i).flip
  have h := pushed.map_mem k hk
  exact MorphismProperty.pushouts_le _ h

/-- Every variable coordinate-switch history has only genuine original cellular steps. -/
theorem coordinateSwitchHistory_mem (P : MorphismProperty C)
    [P.IsStableUnderCobaseChange]
    (hc : ∀ (i : ι) (k : (K i).carrier) (_ : ¬ IsMax k),
      P ((c i).F.map (homOfLE (Order.le_succ k))))
    (s : {s : coordinateOrder (ι := ι) // ¬ IsMax s})
    (k : (coordinateSwitchShape K s).carrier) (hk : ¬ IsMax k) :
    P ((coordinateSwitchHistory f K c s).F.map (homOfLE (Order.le_succ k))) := by
  classical
  rcases s with ⟨s, hs⟩
  induction s using WithTop.recTopCoe with
  | top => exact (hs isMax_top).elim
  | coe b =>
    induction b using WithBot.recBotCoe with
    | bot =>
      have h : Subsingleton (coordinateSwitchShape K ⟨(⊥ : coordinateOrder (ι := ι)),
          hs⟩).carrier := by
        change Subsingleton (ULift.{κ} (Fin 1))
        infer_instance
      exact (hk (fun l hl => le_of_eq (h.elim l k))).elim
    | coe i => exact coordinateInnerHistory_mem f K c P hc i k hk

/-- The actual varying coordinate shapes, with only singleton dummy and greatest stages added. -/
abbrev allCoordinateShapes :=
  originalCompletedFamily (coordinateSwitchShape K)

/-- The actual original coordinate inner linear order. -/
noncomputable local instance coordinateShapeLinearOrder (s : coordinateOrder (ι := ι)) :
    LinearOrder (allCoordinateShapes K s) :=
  (completeOriginalShapes (coordinateSwitchShape K) s).linearOrder
/-- The actual original coordinate inner bottom. -/
noncomputable local instance coordinateShapeOrderBot (s : coordinateOrder (ι := ι)) :
    OrderBot (allCoordinateShapes K s) :=
  (completeOriginalShapes (coordinateSwitchShape K) s).orderBot
/-- The actual original coordinate inner successor. -/
noncomputable local instance coordinateShapeSuccOrder (s : coordinateOrder (ι := ι)) :
    SuccOrder (allCoordinateShapes K s) :=
  (completeOriginalShapes (coordinateSwitchShape K) s).succOrder
local instance (s : coordinateOrder (ι := ι)) : WellFoundedLT (allCoordinateShapes K s) :=
  (completeOriginalShapes (coordinateSwitchShape K) s).wellFounded
local instance : WellFoundedLT (Index (allCoordinateShapes K)) := lexWellFounded
/-- The genuine successor on the dependent sum of the varying coordinate histories. -/
noncomputable local instance coproductFlatSucc : SuccOrder (Index (allCoordinateShapes K)) :=
    flatSuccOrder

/-- A coproduct of supplied cellular arrows with arbitrary varying inner shapes has one actual
presentation. -/
noncomputable def normalizeVariableCoproduct (P : MorphismProperty C)
    (hc : ∀ (i : ι) (k : (K i).carrier) (_ : ¬ IsMax k),
      (MorphismProperty.coproducts.{ν} P).pushouts ((c i).F.map (homOfLE (Order.le_succ k))))
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    (MorphismProperty.coproducts.{ν} P).pushouts.TransfiniteCompositionOfShape
      (Index (allCoordinateShapes K)) (Limits.Sigma.map f) :=
  normalizeOriginalCellular (coordinatePresentation f) (coordinateSwitchShape K)
      (coordinateSwitchHistory f K c)
    P (coordinateSwitchHistory_mem f K c (MorphismProperty.coproducts.{ν} P).pushouts hc)
    emptySource emptyTarget hSource hTarget

end OriginalCoordinateHistories

section ArbitraryOriginalLabels

variable {C : Type u} [Category.{v} C]
variable {ι : Type w} [HasColimitsOfShape (Discrete ι) C]
variable {A B : ι → C} (f : ∀ i, A i ⟶ B i)
variable (K : ι → OriginalInnerShape.{κ})
variable (c : ∀ i, TransfiniteCompositionOfShape (K i).carrier (f i))

/-- The labels of a small original coproduct can be well ordered without changing its objects or
maps. -/
theorem arbitraryCoproductHasPresentation [HasPushouts C] (P : MorphismProperty C)
    (hc : ∀ (i : ι) (k : (K i).carrier) (_ : ¬ IsMax k),
      (MorphismProperty.coproducts.{ν} P).pushouts ((c i).F.map (homOfLE (Order.le_succ k))))
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    ∃ (J : Type (max w κ)) (_ : LinearOrder J) (_ : OrderBot J)
      (_ : SuccOrder J) (_ : WellFoundedLT J),
      Nonempty ((MorphismProperty.coproducts.{ν} P).pushouts.TransfiniteCompositionOfShape J
        (Limits.Sigma.map f)) := by
  classical
  obtain ⟨order, wf⟩ := exists_wellFoundedLT ι
  let _ : LinearOrder ι := order
  let _ : WellFoundedLT ι := wf
  let _ : SuccOrder (MorphismProperty.CoproductCells.cellOrder ι) :=
      SuccOrder.ofLinearWellFoundedLT _
  let D := originalCompletedFamily (coordinateSwitchShape K)
  let _ (s : MorphismProperty.CoproductCells.cellOrder ι) : LinearOrder (D s) :=
    (completeOriginalShapes (coordinateSwitchShape K) s).linearOrder
  let _ (s : MorphismProperty.CoproductCells.cellOrder ι) : OrderBot (D s) :=
    (completeOriginalShapes (coordinateSwitchShape K) s).orderBot
  let _ (s : MorphismProperty.CoproductCells.cellOrder ι) : SuccOrder (D s) :=
    (completeOriginalShapes (coordinateSwitchShape K) s).succOrder
  let _ (s : MorphismProperty.CoproductCells.cellOrder ι) : WellFoundedLT (D s) :=
    (completeOriginalShapes (coordinateSwitchShape K) s).wellFounded
  let _ : WellFoundedLT (Index D) := lexWellFounded
  let _ : SuccOrder (Index D) := flatSuccOrder
  let p := normalizeVariableCoproduct f K c P hc emptySource emptyTarget hSource hTarget
  exact ⟨Index D, inferInstance, inferInstance, inferInstance, inferInstance, ⟨p⟩⟩

end ArbitraryOriginalLabels

end CategoryTheory.SmallObject.CellularNormalization
