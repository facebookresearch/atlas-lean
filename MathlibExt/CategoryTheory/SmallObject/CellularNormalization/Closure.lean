/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.Coproducts
public import MathlibExt.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Closure of actual original cellular presentations

Hovey, *Model Categories* (1999), Lemma 2.1.12, printed p.31 / PDF p.41,
normalizes the original outer and varying inner histories. Lemma 2.1.13,
printed pp.31–32 / PDF pp.41–42, supplies the coproduct construction.

The original orders, root, endpoint and colimit legs are retained by the
existing producers. Independent outer and inner order universes give a single
presentation in their maximum. Empty joins use the actual supplied cofans.
-/

@[expose] public section

noncomputable section

universe w w' κ ν u v

namespace CategoryTheory.SmallObject.CellularNormalization

open Limits

variable {C : Type u} [Category.{v} C]

/-- Actual transfinite compositions of pushouts of coproducts of the original class. -/
abbrev cellularClosure (P : MorphismProperty C) : MorphismProperty C :=
  MorphismProperty.transfiniteCompositions.{w} (P.coproducts.{ν}).pushouts

section OriginalHistories

variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : C} {f : X ⟶ Y} (outer : TransfiniteCompositionOfShape J f)
  (K : {j : J // ¬ IsMax j} → OriginalInnerShape.{w'})
  (c : ∀ i, TransfiniteCompositionOfShape (K i).carrier
    (outer.F.map (homOfLE (Order.le_succ i.1))))

/-- The original inner linear order, or its constructed maximal singleton order. -/
local instance (j : J) : LinearOrder (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).linearOrder
/-- The bottom of the original inner shape, including the maximal singleton case. -/
local instance (j : J) : OrderBot (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).orderBot
/-- The supplied original inner successor, or the actual singleton successor. -/
local instance (j : J) : SuccOrder (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).succOrder
local instance (j : J) : WellFoundedLT (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).wellFounded
local instance : WellFoundedLT (Index (originalCompletedFamily K)) := lexWellFounded
/-- The actual lexicographic successor on the original completed dependent order. -/
local instance : SuccOrder (Index (originalCompletedFamily K)) := flatSuccOrder

/-- A single actual cellular presentation retains the whole original flattened functor,
endpoint cocone and root comparison, on the original completed dependent order. -/
theorem originalHistories_presentation (P : MorphismProperty C)
    (hc : ∀ i k (_ : ¬ IsMax k),
      (P.coproducts.{ν}).pushouts ((c i).F.map (homOfLE (Order.le_succ k))))
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    ∃ d : (P.coproducts.{ν}).pushouts.TransfiniteCompositionOfShape
        (Index (originalCompletedFamily K)) f,
      d.F = diagram outer.F (completeOriginalHistories outer.F K c) ∧
      d.incl ≍ endpoint outer.F (completeOriginalHistories outer.F K c) outer.incl ∧
      d.isoBot ≍ (completeOriginalHistories outer.F K c ⊥).isoBot ≪≫ outer.isoBot := by
  exact ⟨normalizeOriginalCellular outer K c P hc emptySource emptyTarget hSource hTarget,
    rfl, HEq.rfl, HEq.rfl⟩

/-- The supplied original successor histories give one actual presentation of the same f,
in the maximum of the original outer and inner order universes. -/
theorem originalHistories_mem (P : MorphismProperty C)
    (hc : ∀ i k (_ : ¬ IsMax k),
      (P.coproducts.{ν}).pushouts ((c i).F.map (homOfLE (Order.le_succ k))))
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    cellularClosure.{max w w', ν} P f := by
  let d := normalizeOriginalCellular outer K c P hc emptySource emptyTarget hSource hTarget
  exact MorphismProperty.transfiniteCompositionsOfShape_le_transfiniteCompositions
    (P.coproducts.{ν}).pushouts (Index (originalCompletedFamily K)) f d.mem

end OriginalHistories

/-- An actual endpoint pushout carries the original whole cellular history along its
fixed attaching map; all original inner stages keep their supplied shape. -/
theorem cobaseChange_mem (P : MorphismProperty C)
    {A B X Z : C} {f : A ⟶ B} (a : A ⟶ X) [HasPushoutsAlong a]
    {q : X ⟶ Z} {b : B ⟶ Z} (sq : IsPushout a f q b)
    (hf : cellularClosure.{w, ν} P f) : cellularClosure.{w, ν} P q := by
  obtain ⟨J, _, _, _, _, hc⟩ :=
    (MorphismProperty.transfiniteCompositions_iff _ f).1 hf
  let c := Classical.choice hc
  let d := (c.cobaseChange a sq).ofLE
    (MorphismProperty.pushouts_le (P := (P.coproducts.{ν}).pushouts))
  exact MorphismProperty.transfiniteCompositionsOfShape_le_transfiniteCompositions
    (P.coproducts.{ν}).pushouts J q d.mem

section OriginalOrderedCoproduct

variable {I : Type w} [LinearOrder I] [WellFoundedLT I]
  [HasColimitsOfShape (Discrete I) C]
  {A B : I → C} (f : ∀ i, A i ⟶ B i) (K : I → OriginalInnerShape.{κ})
  (c : ∀ i, TransfiniteCompositionOfShape (K i).carrier (f i))
  [∀ i, HasPushoutsAlong (MorphismProperty.CoproductCells.cellSourceInjection f i)]

/-- The successor on the original coordinate chain with its bottom and greatest stages. -/
local instance : SuccOrder (coordinateOrder (ι := I)) := SuccOrder.ofLinearWellFoundedLT _
/-- The original coordinate inner linear order, including the constructed singleton stages. -/
local instance (s : coordinateOrder (ι := I)) : LinearOrder (allCoordinateShapes K s) :=
  (completeOriginalShapes (coordinateSwitchShape K) s).linearOrder
/-- The actual bottom of each original or singleton coordinate history. -/
local instance (s : coordinateOrder (ι := I)) : OrderBot (allCoordinateShapes K s) :=
  (completeOriginalShapes (coordinateSwitchShape K) s).orderBot
/-- The original supplied or singleton successor at each coordinate stage. -/
local instance (s : coordinateOrder (ι := I)) : SuccOrder (allCoordinateShapes K s) :=
  (completeOriginalShapes (coordinateSwitchShape K) s).succOrder
local instance (s : coordinateOrder (ι := I)) : WellFoundedLT (allCoordinateShapes K s) :=
  (completeOriginalShapes (coordinateSwitchShape K) s).wellFounded
local instance : WellFoundedLT (Index (allCoordinateShapes K)) := lexWellFounded
/-- The lexicographic successor for the unchanged original varying coordinate histories. -/
local instance : SuccOrder (Index (allCoordinateShapes K)) := flatSuccOrder

/-- The given varying coordinate histories produce a single presentation at the same
whole Sigma.map f, in the maximum of the coordinate and original inner universes. -/
theorem originalCoproduct_mem (P : MorphismProperty C)
    (hc : ∀ i k (_ : ¬ IsMax k),
      (P.coproducts.{ν}).pushouts ((c i).F.map (homOfLE (Order.le_succ k))))
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    cellularClosure.{max w κ, ν} P (Limits.Sigma.map f) := by
  let d := normalizeVariableCoproduct f K c P hc emptySource emptyTarget hSource hTarget
  exact MorphismProperty.transfiniteCompositionsOfShape_le_transfiniteCompositions
    (P.coproducts.{ν}).pushouts (Index (allCoordinateShapes K)) _ d.mem

end OriginalOrderedCoproduct

/-- Arbitrary original coproduct labels and independent component-history universes
give an actual cellular presentation at the unchanged whole coproduct arrow. -/
theorem coproduct_mem (P : MorphismProperty C) [HasPushouts C]
    {I : Type w} [HasColimitsOfShape (Discrete I) C]
    {A B : I → C} (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, cellularClosure.{w', ν} P (f i))
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    cellularClosure.{max w w', ν} P (Limits.Sigma.map f) := by
  classical
  have hHistories : ∀ i, ∃ S : OriginalInnerShape.{w'},
      Nonempty ((P.coproducts.{ν}).pushouts.TransfiniteCompositionOfShape S.carrier (f i)) := by
    intro i
    obtain ⟨K, hlin, hsucc, hbot, hwf, hc⟩ :=
      (MorphismProperty.transfiniteCompositions_iff _ (f i)).1 (hf i)
    let S : OriginalInnerShape.{w'} :=
      { carrier := K, linearOrder := hlin, orderBot := hbot,
        succOrder := hsucc, wellFounded := hwf }
    exact ⟨S, hc⟩
  choose K hc using hHistories
  let c := fun i => Classical.choice (hc i)
  obtain ⟨J, _, _, _, _, hd⟩ := arbitraryCoproductHasPresentation f K
    (fun i => (c i).toTransfiniteCompositionOfShape) P (fun i k hk => (c i).map_mem k hk)
    emptySource emptyTarget hSource hTarget
  exact MorphismProperty.transfiniteCompositionsOfShape_le_transfiniteCompositions
    (P.coproducts.{ν}).pushouts J _ (Classical.choice hd).mem

/-- The original transfinite chain of cellular arrows is itself cellular. Its actual
original outer order and each occurring inner order determine the working maximum. -/
theorem transfiniteComposition_mem (P : MorphismProperty C)
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {X Y : C} {f : X ⟶ Y}
    (outer : (cellularClosure.{w', ν} P).TransfiniteCompositionOfShape J f)
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    cellularClosure.{max w w', ν} P f := by
  classical
  have hHistories : ∀ i : {j : J // ¬ IsMax j}, ∃ S : OriginalInnerShape.{w'},
      Nonempty ((P.coproducts.{ν}).pushouts.TransfiniteCompositionOfShape S.carrier
        (outer.F.map (homOfLE (Order.le_succ i.1)))) := by
    intro i
    obtain ⟨K, hlin, hsucc, hbot, hwf, hc⟩ :=
      (MorphismProperty.transfiniteCompositions_iff _ _).1 (outer.map_mem i.1 i.2)
    let S : OriginalInnerShape.{w'} :=
      { carrier := K, linearOrder := hlin, orderBot := hbot,
        succOrder := hsucc, wellFounded := hwf }
    exact ⟨S, hc⟩
  choose K hc using hHistories
  let c := fun i => Classical.choice (hc i)
  exact originalHistories_mem outer.toTransfiniteCompositionOfShape K
    (fun i => (c i).toTransfiniteCompositionOfShape) P (fun i k hk => (c i).map_mem k hk)
    emptySource emptyTarget hSource hTarget

/-- At a working order universe the actual cellular class is closed under coproducts,
cobase change and transfinite composition, with its supplied empty-cell witnesses. -/
theorem cellularClosure_stable (P : MorphismProperty C)
    [HasPushouts C] [HasCoproducts.{w} C]
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    (cellularClosure.{w, ν} P).IsStableUnderCobaseChange ∧
      (cellularClosure.{w, ν} P).IsStableUnderCoproducts.{w} ∧
      MorphismProperty.IsStableUnderTransfiniteComposition.{w} (cellularClosure.{w, ν} P) := by
  let Q := cellularClosure.{w, ν} P
  have hco : Q.IsStableUnderCobaseChange :=
    { of_isPushout := fun sq hf => cobaseChange_mem P _ sq hf }
  let : Q.IsStableUnderCobaseChange := hco
  have hcop : Q.IsStableUnderCoproducts.{w} :=
    { isStableUnderCoproductsOfShape := fun I =>
        .mk Q I (fun _ _ _ _ f hf => coproduct_mem P f hf
          emptySource emptyTarget hSource hTarget) }
  have htc : MorphismProperty.IsStableUnderTransfiniteComposition.{w} Q :=
    { isStableUnderTransfiniteCompositionOfShape := fun J _ _ _ _ =>
        { le := fun _ _ _ ⟨outer⟩ => transfiniteComposition_mem P outer
            emptySource emptyTarget hSource hTarget } }
  exact ⟨hco, hcop, htc⟩

end CategoryTheory.SmallObject.CellularNormalization
