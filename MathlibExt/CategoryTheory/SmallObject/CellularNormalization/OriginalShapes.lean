/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.Attachments
public import Mathlib.Order.SuccPred.Fin
public import Mathlib.Order.ULift

/-!
# Original nonmaximal histories keep their complete shapes and maps

Construct only singleton histories at original maximal vertices. Retain every
supplied original nonmaximal shape, order, history, map and endpoint cocone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u v w w' ν

namespace CategoryTheory.SmallObject.CellularNormalization

section MaximalSingletons

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [LinearOrder J] [SuccOrder J]
variable (F : J ⥤ C)

/-- A maximal original outer vertex has the actual trivial one-stage inner presentation. -/
noncomputable def maximalInner (j : J) (hj : IsMax j) :
    TransfiniteCompositionOfShape (Fin 1) (F.map (homOfLE (Order.le_succ j))) := by
  let e : F.obj j ≅ F.obj (Order.succ j) := F.mapIso (eqToIso hj.succ_eq.symm)
  let base := TransfiniteCompositionOfShape.ofComposableArrows (ComposableArrows.mk₀ (F.obj j))
  exact base.ofArrowIso (Arrow.isoMk (Iso.refl _) e (by
    change (𝟙 _) ≫ F.map (homOfLE (Order.le_succ j)) = (𝟙 _) ≫ F.map (eqToHom hj.succ_eq.symm)
    exact congrArg (fun t => (𝟙 _) ≫ F.map t) (Subsingleton.elim _ _)))

variable (K : {j : J // ¬ IsMax j} → Type w')
  [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)] [∀ j, OrderBot (K j)]
  [∀ j, WellFoundedLT (K j)]

/-- The actual supplied nonmaximal shapes, with a genuine singleton only at original maximal
vertices. -/
noncomputable def completedInnerShape (j : J) : Type w' := by
  classical
  exact if hj : IsMax j then ULift.{w'} (Fin 1) else K ⟨j, hj⟩

omit [SuccOrder J] [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)] [∀ j, OrderBot (K j)]
  [∀ j, WellFoundedLT (K j)] in
/-- No original supplied nonmaximal inner shape is replaced. -/
theorem completedInnerShape_nonmax (j : J) (hj : ¬ IsMax j) :
    completedInnerShape K j = K ⟨j, hj⟩ := by
  classical
  simp [completedInnerShape, hj]

omit [SuccOrder J] [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)] [∀ j, OrderBot (K j)]
  [∀ j, WellFoundedLT (K j)] in
/-- The constructed maximal shape has no genuine cell step. -/
theorem completedInnerShape_max (j : J) (hj : IsMax j) :
    completedInnerShape K j = ULift.{w'} (Fin 1) := by
  classical
  simp [completedInnerShape, hj]

end MaximalSingletons

section OriginalShapeRecords

/-- An original small inner shape with its actual well-ordered successor data. -/
structure OriginalInnerShape where
  /-- The actual original small inner-order type. -/
  carrier : Type w'
  /-- Its actual supplied linear order. -/
  linearOrder : LinearOrder carrier
  /-- Its original bottom vertex. -/
  orderBot : @OrderBot carrier linearOrder.toLE
  /-- Its original successor structure. -/
  succOrder : @SuccOrder carrier linearOrder.toPreorder
  /-- The well-founded strict order of the original shape. -/
  wellFounded : @WellFoundedLT carrier linearOrder.toLT

attribute [instance] OriginalInnerShape.linearOrder OriginalInnerShape.orderBot
  OriginalInnerShape.succOrder OriginalInnerShape.wellFounded

variable {J : Type w} [LinearOrder J]

/-- The actual supplied shape is retained at every nonmaximal original outer vertex. -/
noncomputable def completeOriginalShapes (K : {j : J // ¬ IsMax j} → OriginalInnerShape.{w'})
    (j : J) : OriginalInnerShape.{w'} := by
  classical
  exact if hj : IsMax j then
    { carrier := ULift.{w'} (Fin 1)
      linearOrder := inferInstance
      orderBot := inferInstance
      succOrder := SuccOrder.ofLinearWellFoundedLT (ULift.{w'} (Fin 1))
      wellFounded := inferInstance }
    else K ⟨j, hj⟩

/-- Nonmaximal completion is equality with the entire original supplied shape and all its order
data. -/
theorem completeOriginalShapes_nonmax (K : {j : J // ¬ IsMax j} → OriginalInnerShape.{w'})
    (j : J) (hj : ¬ IsMax j) : completeOriginalShapes K j = K ⟨j, hj⟩ := by
  classical
  simp [completeOriginalShapes, hj]


variable {C : Type u} [Category.{v} C] [SuccOrder J] (F : J ⥤ C)

/-- The supplied genuine successor histories are extended by constructed maximal singleton
histories. -/
noncomputable def completeOriginalHistories
    (K : {j : J // ¬ IsMax j} → OriginalInnerShape.{w'})
    (c : ∀ i : {j : J // ¬ IsMax j},
      TransfiniteCompositionOfShape (K i).carrier (F.map (homOfLE (Order.le_succ i.1))))
    (j : J) :
    TransfiniteCompositionOfShape (completeOriginalShapes K j).carrier
      (F.map (homOfLE (Order.le_succ j))) := by
  classical
  by_cases hj : IsMax j
  · let singleton : OriginalInnerShape.{w'} :=
      { carrier := ULift.{w'} (Fin 1)
        linearOrder := inferInstance
        orderBot := inferInstance
        succOrder := SuccOrder.ofLinearWellFoundedLT (ULift.{w'} (Fin 1))
        wellFounded := inferInstance }
    let _ : LinearOrder singleton.carrier := singleton.linearOrder
    let _ : OrderBot singleton.carrier := singleton.orderBot
    let _ : SuccOrder singleton.carrier := singleton.succOrder
    let _ : WellFoundedLT singleton.carrier := singleton.wellFounded
    let E : singleton.carrier ≃o Fin 1 :=
      { toEquiv := Equiv.ulift
        map_rel_iff' := Iff.rfl }
    let base : TransfiniteCompositionOfShape singleton.carrier
        (F.map (homOfLE (Order.le_succ j))) := (maximalInner F j hj).ofOrderIso E
    have he : completeOriginalShapes K j = singleton := by
      simp [completeOriginalShapes, hj, singleton]
    exact he.symm ▸ base
  · exact (completeOriginalShapes_nonmax K j hj).symm ▸ c ⟨j, hj⟩

/-- A completed nonmaximal history is the original supplied history, including all maps and
cocones. -/
theorem completeOriginalHistories_nonmax
    (K : {j : J // ¬ IsMax j} → OriginalInnerShape.{w'})
    (c : ∀ i : {j : J // ¬ IsMax j},
      TransfiniteCompositionOfShape (K i).carrier (F.map (homOfLE (Order.le_succ i.1))))
    (j : J) (hj : ¬ IsMax j) :
    completeOriginalHistories F K c j ≍ c ⟨j, hj⟩ := by
  unfold completeOriginalHistories
  simp only [dite_eq_right hj]
  exact eqRec_heq
    (φ := fun T : OriginalInnerShape.{w'} =>
      TransfiniteCompositionOfShape T.carrier (F.map (homOfLE (Order.le_succ j))))
    (completeOriginalShapes_nonmax K j hj).symm (c ⟨j, hj⟩)

end OriginalShapeRecords

section OriginalCellularCompletion

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {X Y : C} {f : X ⟶ Y} (outer : TransfiniteCompositionOfShape J f)
variable (K : {j : J // ¬ IsMax j} → OriginalInnerShape.{w'})

/-- The actual all-vertex family after adding only genuine singleton maximal blocks. -/
abbrev originalCompletedFamily := fun j => (completeOriginalShapes K j).carrier

/-- The original or constructed singleton linear order at each outer vertex. -/
noncomputable local instance originalCompletedLinearOrder (j : J) :
    LinearOrder (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).linearOrder
/-- The original or constructed singleton bottom at each outer vertex. -/
noncomputable local instance originalCompletedOrderBot (j : J) :
    OrderBot (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).orderBot
/-- The original or constructed singleton successor at each outer vertex. -/
noncomputable local instance originalCompletedSuccOrder (j : J) :
    SuccOrder (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).succOrder
local instance (j : J) : WellFoundedLT (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).wellFounded

local instance : WellFoundedLT (Index (originalCompletedFamily K)) := lexWellFounded
/-- The genuine lexicographic successor for original nonmaximal-only input histories. -/
noncomputable local instance originalNormalizationSuccOrder :
    SuccOrder (Index (originalCompletedFamily K)) := flatSuccOrder

variable (c : ∀ i : {j : J // ¬ IsMax j},
  TransfiniteCompositionOfShape (K i).carrier (outer.F.map (homOfLE (Order.le_succ i.1))))

/-- Successor membership transports along equality of whole original shapes and actual histories. -/
theorem mapMembershipOfShapeEq (P : MorphismProperty C)
    {S T : OriginalInnerShape.{w'}} (e : S = T)
    {Z W : C} {q : Z ⟶ W}
    (d : TransfiniteCompositionOfShape S.carrier q)
    (d' : TransfiniteCompositionOfShape T.carrier q) (hd : d ≍ d')
    (h : ∀ (k : T.carrier) (_ : ¬ IsMax k), P (d'.F.map (homOfLE (Order.le_succ k))))
    (k : S.carrier) (hk : ¬ IsMax k) : P (d.F.map (homOfLE (Order.le_succ k))) := by
  subst T
  have he := eq_of_heq hd
  subst d'
  exact h k hk

/-- Original successor membership extends to every actual genuine inner step; maximal singleton
blocks have none. -/
theorem completeOriginalHistories_map_mem (P : MorphismProperty C)
    (hc : ∀ (i : {j : J // ¬ IsMax j}) (k : (K i).carrier) (_ : ¬ IsMax k),
      P ((c i).F.map (homOfLE (Order.le_succ k))))
    (j : J) (k : originalCompletedFamily K j) (hk : ¬ IsMax k) :
    P ((completeOriginalHistories outer.F K c j).F.map (homOfLE (Order.le_succ k))) := by
  classical
  by_cases hj : IsMax j
  · have hs : Subsingleton (originalCompletedFamily K j) := by
      unfold originalCompletedFamily completeOriginalShapes
      simp only [dite_eq_left hj]
      infer_instance
    have hmax : IsMax k := fun i h => le_of_eq (hs.elim i k)
    exact (hk hmax).elim
  · exact mapMembershipOfShapeEq P (completeOriginalShapes_nonmax K j hj)
      (completeOriginalHistories outer.F K c j) (c ⟨j, hj⟩)
      (completeOriginalHistories_nonmax outer.F K c j hj) (hc ⟨j, hj⟩) k hk

/-- Normalize genuine original successor cellular histories, allowing arbitrary varying shapes and
maximal inner stages. -/
noncomputable def normalizeOriginalCellular (P : MorphismProperty C)
    (hc : ∀ (i : {j : J // ¬ IsMax j}) (k : (K i).carrier) (_ : ¬ IsMax k),
      (MorphismProperty.coproducts.{ν} P).pushouts ((c i).F.map (homOfLE (Order.le_succ k))))
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    (MorphismProperty.coproducts.{ν} P).pushouts.TransfiniteCompositionOfShape
      (Index (originalCompletedFamily K)) f :=
  normalizeCellular outer (completeOriginalHistories outer.F K c) P
    (completeOriginalHistories_map_mem outer K c (MorphismProperty.coproducts.{ν} P).pushouts hc)
    emptySource emptyTarget hSource hTarget

end OriginalCellularCompletion

end CategoryTheory.SmallObject.CellularNormalization
