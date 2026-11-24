/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.Coproducts
import Lean.Elab.Command

/-!
# Public tests for original variable cellular normalization

Finite clients exercise genuine inner successors, greatest-inner joins with
the supplied empty cofans, and maximal singleton completion. Polymorphic
coproduct clients keep the coordinate, inner, cell, object and Hom universes
independent and check the unchanged whole endpoint arrow.
-/

@[expose] public section

noncomputable section

universe w κ ν t u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.SmallObject.CellularNormalization

namespace MathlibExtTest.CategoryTheory.SmallObject.CellularNormalizationTests

theorem zero_nonmax : ¬ IsMax (0 : Fin 2) := by
  intro h
  exact h.not_lt (by decide : (0 : Fin 2) < 1)

theorem one_max : IsMax (1 : Fin 2) := isMax_top

abbrev finiteInner (_ : Fin 2) := Fin 2

local instance : WellFoundedLT (Index finiteInner) := lexWellFounded
local instance : SuccOrder (Index finiteInner) := flatSuccOrder

-- These distinguish a real inner step from the greatest-inner boundary join.
example : Order.succ (vertex (0 : Fin 2) (0 : finiteInner 0)) = vertex 0 1 := by
  have hs : Order.succ (0 : Fin 2) = 1 := Fin.orderSucc_castSucc (0 : Fin 1)
  simpa only [hs] using flat_succ_inner (K := finiteInner) 0 0 zero_nonmax

example : Order.succ (vertex (0 : Fin 2) (1 : finiteInner 0)) = vertex 1 0 := by
  have h := flat_succ_join (K := finiteInner) 0 1 zero_nonmax one_max
  exact h.trans (by congr 1)

private theorem inner_vertex_nonmax : ¬ IsMax (vertex (0 : Fin 2) (0 : finiteInner 0)) :=
  fun h => zero_nonmax ((flat_isMax_iff 0 0).1 h).2

private theorem join_vertex_nonmax : ¬ IsMax (vertex (0 : Fin 2) (1 : finiteInner 0)) :=
  fun h => zero_nonmax ((flat_isMax_iff 0 1).1 h).1

example : IsMax (vertex (1 : Fin 2) (1 : finiteInner 1)) :=
  (flat_isMax_iff 1 1).2 ⟨one_max, one_max⟩

section FiniteOriginalDiagrams

variable {C : Type u} [Category.{v} C] (F : Fin 2 ⥤ C)
  (c : ∀ j, TransfiniteCompositionOfShape (finiteInner j)
    (F.map (homOfLE (Order.le_succ j))))

-- The actual inner map and literal block restriction remain available publicly.
example : (diagram F c).map
    (homOfLE (show vertex (0 : Fin 2) (0 : finiteInner 0) ≤ vertex 0 1 from
      Sigma.Lex.right _ _ (by decide))) =
    (c 0).F.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)) :=
  diagram_inner_map F c 0 (by decide)

example : blockInclusion (K := finiteInner) 0 ⋙ diagram F c = (c 0).F :=
  block_restriction F c 0

end FiniteOriginalDiagrams

section FiniteOriginalAttachments

variable {C : Type u} [Category.{v} C]
  {α : Fin 2 → Type t} {A B : ∀ j, α j → C} (g : ∀ j a, A j a ⟶ B j a)
  {X Y : C} {f : X ⟶ Y} (outer : TransfiniteCompositionOfShape (Fin 2) f)
  (c : ∀ j, RelativeCellComplex.{ν} (fun _ : finiteInner j => g j)
    (outer.F.map (homOfLE (Order.le_succ j))))
  (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget)

-- A genuine inner successor keeps the original generator labels and whole cofan.
example : (innerAttachment g outer c 0 0 zero_nonmax).ι =
    ((c 0).attachCells 0 zero_nonmax).ι :=
  innerAttachment_labels g outer c 0 0 zero_nonmax

example : (innerAttachment g outer c 0 0 zero_nonmax).cofan₁ ≍
    ((c 0).attachCells 0 zero_nonmax).cofan₁ :=
  innerAttachment_sourceCofan g outer c 0 0 zero_nonmax

-- The public empty-cell constructor is applied to the actual greatest-inner join.
def greatestJoinCells : AttachCells.{ν} (g 0)
    (crossMap outer.F (innerPresentations g outer c)
      (Order.lt_succ_iff_not_isMax.mpr zero_nonmax) (1 : finiteInner 0)
      (⊥ : finiteInner (Order.succ (0 : Fin 2)))) := by
  letI := join_isIso outer (innerPresentations g outer c) 0 1 zero_nonmax one_max
  exact emptyAttachCells (g 0) _ emptySource emptyTarget hSource hTarget

example : IsEmpty (greatestJoinCells g outer c emptySource emptyTarget hSource hTarget).ι := by
  change IsEmpty PEmpty.{ν + 1}
  infer_instance

example : (greatestJoinCells g outer c emptySource emptyTarget hSource hTarget).cofan₁.pt =
    emptySource.pt := rfl

example : (greatestJoinCells g outer c emptySource emptyTarget hSource hTarget).cofan₂.pt =
    emptyTarget.pt := rfl

-- Normalization derives membership at this join from the input inner steps and the empty cofans.
example (P : MorphismProperty C)
    (hc : ∀ j k (_ : ¬ IsMax k), (P.coproducts.{ν}).pushouts
      ((c j).F.map (homOfLE (Order.le_succ k)))) :
    (P.coproducts.{ν}).pushouts
      ((diagram outer.F (innerPresentations g outer c)).map
        (homOfLE (Order.le_succ (vertex (0 : Fin 2) (1 : finiteInner 0))))) :=
  (normalizeCellular outer (innerPresentations g outer c) P hc
    emptySource emptyTarget hSource hTarget).map_mem _ join_vertex_nonmax

-- The final leg still follows the original inner leg and the original outer cocone.
example : (normalizedPresentation outer (innerPresentations g outer c)).incl.app
    (vertex (0 : Fin 2) (1 : finiteInner 0)) =
    (c 0).incl.app 1 ≫ outer.incl.app (Order.succ (0 : Fin 2)) :=
  normalizedPresentation_incl outer (innerPresentations g outer c) 0 1

end FiniteOriginalAttachments

def originalTwoStage : OriginalInnerShape.{0} where
  carrier := Fin 2
  linearOrder := inferInstance
  orderBot := inferInstance
  succOrder := inferInstance
  wellFounded := inferInstance

abbrev suppliedShapes (_ : {j : Fin 2 // ¬ IsMax j}) := originalTwoStage

-- Nonmaximal completion retains the whole supplied order dictionary.
example : completeOriginalShapes suppliedShapes (0 : Fin 2) = originalTwoStage :=
  completeOriginalShapes_nonmax suppliedShapes 0 zero_nonmax

-- Only the maximal original vertex receives the one-stage completion, with no genuine step.
example : (completeOriginalShapes suppliedShapes (1 : Fin 2)).carrier = ULift.{0} (Fin 1) := by
  classical
  simp only [completeOriginalShapes, dite_eq_left one_max]

example : Subsingleton (completeOriginalShapes suppliedShapes (1 : Fin 2)).carrier := by
  classical
  simpa only [completeOriginalShapes, dite_eq_left one_max] using
    (inferInstance : Subsingleton (ULift.{0} (Fin 1)))

example {C : Type u} [Category.{v} C] (F : Fin 2 ⥤ C)
    (c : ∀ i : {j : Fin 2 // ¬ IsMax j}, TransfiniteCompositionOfShape
      (suppliedShapes i).carrier (F.map (homOfLE (Order.le_succ i.1)))) :
    completeOriginalHistories F suppliedShapes c 0 ≍ c ⟨0, zero_nonmax⟩ :=
  completeOriginalHistories_nonmax F suppliedShapes c 0 zero_nonmax

section VariableCoproduct

variable {C : Type u} [Category.{v} C]
  {I : Type w} [LinearOrder I] [WellFoundedLT I]
  [HasColimitsOfShape (Discrete I) C]
  {A B : I → C} (f : ∀ i, A i ⟶ B i) (K : I → OriginalInnerShape.{κ})
  (c : ∀ i, TransfiniteCompositionOfShape (K i).carrier (f i))
  [∀ i, HasPushoutsAlong (MorphismProperty.CoproductCells.cellSourceInjection f i)]
  (P : MorphismProperty C)
  (hc : ∀ i k (_ : ¬ IsMax k),
    (P.coproducts.{ν}).pushouts ((c i).F.map (homOfLE (Order.le_succ k))))
  (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget)

local instance : SuccOrder (coordinateOrder (ι := I)) := SuccOrder.ofLinearWellFoundedLT _
local instance (s : coordinateOrder (ι := I)) : LinearOrder (allCoordinateShapes K s) :=
  (completeOriginalShapes (coordinateSwitchShape K) s).linearOrder
local instance (s : coordinateOrder (ι := I)) : OrderBot (allCoordinateShapes K s) :=
  (completeOriginalShapes (coordinateSwitchShape K) s).orderBot
local instance (s : coordinateOrder (ι := I)) : SuccOrder (allCoordinateShapes K s) :=
  (completeOriginalShapes (coordinateSwitchShape K) s).succOrder
local instance (s : coordinateOrder (ι := I)) : WellFoundedLT (allCoordinateShapes K s) :=
  (completeOriginalShapes (coordinateSwitchShape K) s).wellFounded
local instance : WellFoundedLT (Index (allCoordinateShapes K)) := lexWellFounded
local instance : SuccOrder (Index (allCoordinateShapes K)) := flatSuccOrder

-- No global pushout assumption is needed by the fixed original-coordinate producer.
example : Nonempty ((P.coproducts.{ν}).pushouts.TransfiniteCompositionOfShape
    (Index (allCoordinateShapes K)) (Limits.Sigma.map f)) :=
  ⟨normalizeVariableCoproduct f K c P hc emptySource emptyTarget hSource hTarget⟩

example :
    let d := normalizeVariableCoproduct f K c P hc emptySource emptyTarget hSource hTarget
    d.isoBot.inv ≫ d.incl.app ⊥ = Limits.Sigma.map f := by
  dsimp only
  exact (normalizeVariableCoproduct f K c P hc emptySource emptyTarget hSource hTarget).fac

end VariableCoproduct

section UnorderedCoproduct

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {I : Type w} [HasColimitsOfShape (Discrete I) C]
  {A B : I → C} (f : ∀ i, A i ⟶ B i) (K : I → OriginalInnerShape.{κ})
  (c : ∀ i, TransfiniteCompositionOfShape (K i).carrier (f i))
  (P : MorphismProperty C)
  (hc : ∀ i k (_ : ¬ IsMax k),
    (P.coproducts.{ν}).pushouts ((c i).F.map (homOfLE (Order.le_succ k))))
  (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget)

-- The original labels need no supplied order; the result keeps their actual Sigma.map f.
example : ∃ (J : Type (max w κ)) (_ : LinearOrder J) (_ : OrderBot J)
    (_ : SuccOrder J) (_ : WellFoundedLT J),
    Nonempty ((P.coproducts.{ν}).pushouts.TransfiniteCompositionOfShape J (Limits.Sigma.map f)) :=
  arbitraryCoproductHasPresentation f K c P hc emptySource emptyTarget hSource hTarget

end UnorderedCoproduct

def originalSingleton : OriginalInnerShape.{0} where
  carrier := Fin 1
  linearOrder := inferInstance
  orderBot := inferInstance
  succOrder := inferInstance
  wellFounded := inferInstance

def variedShapes (i : Fin 2) : OriginalInnerShape.{0} :=
  if i = 0 then originalTwoStage else originalSingleton

def variedMaps {C : Type u} [Category.{v} C] {A : C} (f : A ⟶ A) (i : Fin 2) : A ⟶ A :=
  if i = 0 then f else 𝟙 A

-- These actual input histories are constructed from an arbitrary map and an identity;
-- their carriers are Fin 2 and Fin 1, respectively.
def variedHistory {C : Type u} [Category.{v} C] {A : C} (f : A ⟶ A) (i : Fin 2) :
    TransfiniteCompositionOfShape (variedShapes i).carrier (variedMaps f i) := by
  classical
  by_cases hi : i = 0
  · have he : variedShapes i = originalTwoStage := by
      unfold variedShapes
      exact ite_eq_left hi
    have hm : variedMaps f i = f := by
      unfold variedMaps
      exact ite_eq_left hi
    let base : TransfiniteCompositionOfShape originalTwoStage.carrier f :=
      TransfiniteCompositionOfShape.ofComposableArrows (ComposableArrows.mk₁ f)
    let d : TransfiniteCompositionOfShape (variedShapes i).carrier f := he.symm ▸ base
    exact hm.symm ▸ d
  · have he : variedShapes i = originalSingleton := by
      unfold variedShapes
      exact ite_eq_right hi
    have hm : variedMaps f i = 𝟙 A := by
      unfold variedMaps
      exact ite_eq_right hi
    let base : TransfiniteCompositionOfShape originalSingleton.carrier (𝟙 A) :=
      TransfiniteCompositionOfShape.ofComposableArrows (ComposableArrows.mk₀ A)
    let d : TransfiniteCompositionOfShape (variedShapes i).carrier (𝟙 A) := he.symm ▸ base
    exact hm.symm ▸ d

example {C : Type u} [Category.{v} C] [HasPushouts C]
    [HasColimitsOfShape (Discrete (Fin 2)) C] {A : C} (f : A ⟶ A)
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    ∃ (J : Type) (_ : LinearOrder J) (_ : OrderBot J) (_ : SuccOrder J) (_ : WellFoundedLT J),
      Nonempty (((⊤ : MorphismProperty C).coproducts.{ν}).pushouts.TransfiniteCompositionOfShape J
        (Limits.Sigma.map (variedMaps f))) := by
  apply arbitraryCoproductHasPresentation (variedMaps f) variedShapes (variedHistory f) ⊤
    (fun i k hk => ?_) emptySource emptyTarget hSource hTarget
  exact ((⊤ : MorphismProperty C).coproducts.{ν}).le_pushouts _
    ((⊤ : MorphismProperty C).le_coproducts _ trivial)

-- A newly introduced nonstandard axiom in any principal producer fails this committed gate.
open Lean Elab Command in
run_cmd do
  let principals : List Name :=
    [ `CategoryTheory.SmallObject.CellularNormalization.diagram
    , `CategoryTheory.SmallObject.CellularNormalization.endpointIsColimit
    , `CategoryTheory.SmallObject.CellularNormalization.diagramIsWellOrderContinuous
    , `CategoryTheory.SmallObject.CellularNormalization.flatSuccOrder
    , `CategoryTheory.SmallObject.CellularNormalization.normalizedPresentation
    , `CategoryTheory.SmallObject.CellularNormalization.normalizeCellular
    , `CategoryTheory.SmallObject.CellularNormalization.normalizeRelativeCells
    , `CategoryTheory.SmallObject.CellularNormalization.normalizeOriginalCellular
    , `CategoryTheory.SmallObject.CellularNormalization.normalizeVariableCoproduct
    , `CategoryTheory.SmallObject.CellularNormalization.arbitraryCoproductHasPresentation ]
  let allowed : List Name := [`propext, `Quot.sound, `Classical.choice]
  for name in principals do
    let axioms ← Lean.collectAxioms name
    unless axioms.toList.all (fun ax => allowed.contains ax) do
      throwError "unexpected principal axiom in {name}: {axioms}"
  logInfo m!"CELLULAR_NORMALIZATION_PRINCIPAL_AXIOMS_OK {principals.length}"

end MathlibExtTest.CategoryTheory.SmallObject.CellularNormalizationTests
