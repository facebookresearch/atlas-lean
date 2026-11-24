/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.SingleObj.Descent
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.Fin
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Actual strict object-adjustment clients

The stock induced groupoids have two overlap objects inside four ambient
objects. Noncommuting permutations give a nontrivial original image arrow
and a nontrivial original arrow between the two outside objects. The actual
object adjustment makes the image restriction strictly constant, preserves
the outside arrow, and preserves every original outside based End value.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MathlibExtTest.SingleObjDescent

abbrev Perm3 := Equiv.Perm (Fin 3)

def firstSwap : Perm3 := Equiv.swap 0 1

def secondSwap : Perm3 := Equiv.swap 1 2

/-- Four actual objects, with the stock groupoid induced from the one-object trivial group. -/
abbrev FourObjects :=
  InducedCategory (SingleObj PUnit.{1}) (fun _ : Fin 4 => SingleObj.star PUnit.{1})

def four (i : Fin 4) : FourObjects := i

def fourIndex (i : FourObjects) : Fin 4 := i

/-- The stock embedding places the two overlap objects at ambient zero and one. -/
def inclusionOnObjects : Fin 2 → FourObjects :=
  fun i => Fin.castAddEmb 2 i

/-- The source uses the stock category induced along that actual object map. -/
abbrev TwoObjects := InducedCategory FourObjects inclusionOnObjects

def two (i : Fin 2) : TwoObjects := i

def overlapInclusion : TwoObjects ⥤ FourObjects := inducedFunctor inclusionOnObjects

/-- An image weight has order three; the outside difference is a nontrivial commutator. -/
def fullWeights : FourObjects → Perm3 :=
  fun i => if fourIndex i = 0 then firstSwap * secondSwap
    else if fourIndex i = 1 then firstSwap
    else if fourIndex i = 2 then firstSwap * secondSwap else secondSwap * firstSwap

def fullFunctor : FourObjects ⥤ SingleObj Perm3 :=
  SingleObj.differenceFunctor fullWeights

def overlapWeights : TwoObjects → Perm3 :=
  fun i => fullWeights (overlapInclusion.obj i)

def adjustedFunctor : FourObjects ⥤ SingleObj Perm3 :=
  SingleObj.objectAdjustment overlapInclusion fullFunctor overlapWeights

def singleObjValue {a b : SingleObj Perm3} (f : a ⟶ b) : Perm3 := f

def fullValue {a b : FourObjects} (f : a ⟶ b) : Perm3 :=
  singleObjValue (fullFunctor.map f)

def adjustedValue {a b : FourObjects} (f : a ⟶ b) : Perm3 :=
  singleObjValue (adjustedFunctor.map f)

/-- A concrete original overlap arrow, constructed with both stock induced-Hom wrappers. -/
def imageArrow : two 0 ⟶ two 1 :=
  InducedCategory.homMk (InducedCategory.homMk (1 : PUnit.{1}))

def outsideArrow : four 2 ⟶ four 3 :=
  InducedCategory.homMk (1 : PUnit.{1})

def crossBoundaryArrow : four 0 ⟶ four 3 :=
  InducedCategory.homMk (1 : PUnit.{1})

theorem inclusionInjective : Function.Injective overlapInclusion.obj := by
  change Function.Injective (Fin.castAddEmb 2 : Fin 2 → Fin 4)
  exact (Fin.castAddEmb 2).injective

theorem imageObjectsClient :
    overlapInclusion.obj (two 0) = four 0 ∧
      overlapInclusion.obj (two 1) = four 1 := by
  exact ⟨rfl, rfl⟩

theorem outsideObjectsClient :
    four 2 ∉ Set.range overlapInclusion.obj ∧
      four 3 ∉ Set.range overlapInclusion.obj := by
  constructor
  · change ¬ ∃ i : Fin 2, (Fin.castAddEmb 2 i : Fin 4) = 2
    decide
  · change ¬ ∃ i : Fin 2, (Fin.castAddEmb 2 i : Fin 4) = 3
    decide

/-- The actual original functor derives the required formula on every overlap arrow. -/
theorem imageFormulaClient {c d : TwoObjects} (f : c ⟶ d) :
    (fullFunctor.map (overlapInclusion.map f) : Perm3) =
      overlapWeights d * (overlapWeights c)⁻¹ := by
  rfl

theorem noncommutingWeightsClient : firstSwap * secondSwap ≠ secondSwap * firstSwap := by
  have hLeft : (firstSwap * secondSwap) (0 : Fin 3) = (1 : Fin 3) := by decide
  have hRight : (secondSwap * firstSwap) (0 : Fin 3) = (2 : Fin 3) := by decide
  intro h
  have hPoint := congrArg (fun p : Perm3 => p (0 : Fin 3)) h
  exact (by decide : (1 : Fin 3) ≠ 2) (hLeft.symm.trans (hPoint.trans hRight))

/-- Strict equality covers the original image objects and all its original arrows. -/
theorem strictRestrictionClient :
    overlapInclusion ⋙ adjustedFunctor =
      (Functor.const TwoObjects).obj (SingleObj.star Perm3) := by
  exact SingleObj.comp_objectAdjustment_eq_const overlapInclusion fullFunctor overlapWeights
    inclusionInjective imageFormulaClient

theorem imageWeightClient :
    SingleObj.objectAdjustmentWeight overlapInclusion overlapWeights (four 0) =
        (firstSwap * secondSwap)⁻¹ ∧
      SingleObj.objectAdjustmentWeight overlapInclusion overlapWeights (four 1) =
        firstSwap⁻¹ := by
  exact ⟨SingleObj.objectAdjustmentWeight_obj overlapInclusion overlapWeights inclusionInjective
      (two 0),
    SingleObj.objectAdjustmentWeight_obj overlapInclusion overlapWeights inclusionInjective
      (two 1)⟩

theorem outsideWeightClient :
    SingleObj.objectAdjustmentWeight overlapInclusion overlapWeights (four 2) = 1 ∧
      SingleObj.objectAdjustmentWeight overlapInclusion overlapWeights (four 3) = 1 := by
  exact ⟨SingleObj.objectAdjustmentWeight_of_not_mem_range overlapInclusion overlapWeights
      (four 2) outsideObjectsClient.1,
    SingleObj.objectAdjustmentWeight_of_not_mem_range overlapInclusion overlapWeights
      (four 3) outsideObjectsClient.2⟩

/-- The original image arrow is nontrivial, with its noncommutative order visible at zero. -/
theorem imageArrowBeforeClient :
    (fullValue (overlapInclusion.map imageArrow)) (0 : Fin 3) = 2 := by
  decide

theorem imageArrowKilledClient :
    adjustedValue (overlapInclusion.map imageArrow) = 1 := by
  have h := SingleObj.objectAdjustment_map_map overlapInclusion fullFunctor overlapWeights
    inclusionInjective imageFormulaClient imageArrow
  exact congrArg singleObjValue h

/-- The original outside arrow is the nontrivial difference of the original weights at 3 and 2. -/
theorem outsideArrowBeforeClient :
    fullValue outsideArrow =
        (secondSwap * firstSwap) * (firstSwap * secondSwap)⁻¹ ∧
      (fullValue outsideArrow) (0 : Fin 3) = 1 := by
  constructor
  · rfl
  · decide

/-- Preservation retains a genuinely nonidentity arrow between two different outside objects. -/
theorem outsideArrowPreservationClient :
    adjustedValue outsideArrow = fullValue outsideArrow ∧
      adjustedValue outsideArrow ≠ 1 := by
  have hPreserved :
      adjustedValue outsideArrow = fullValue outsideArrow := by
    have h := SingleObj.objectAdjustment_map_of_not_mem_range
      overlapInclusion fullFunctor overlapWeights outsideArrow
        outsideObjectsClient.1 outsideObjectsClient.2
    exact congrArg singleObjValue h
  refine ⟨hPreserved, ?_⟩
  intro h
  have hPoint := congrArg (fun p : Perm3 => p (0 : Fin 3)) (hPreserved.symm.trans h)
  have hBad : (1 : Fin 3) = 0 := outsideArrowBeforeClient.2.symm.trans hPoint
  exact (by decide : (1 : Fin 3) ≠ 0) hBad

/-- The original reversed End values at an outside object are preserved for every e. -/
theorem outsideEndRecoveryClient (e : End (four 2)) :
    (((adjustedFunctor.mapEnd (four 2)) e).asHom : Perm3) =
      (((fullFunctor.mapEnd (four 2)) e).asHom : Perm3) := by
  exact SingleObj.objectAdjustment_mapEnd_of_not_mem_range
    overlapInclusion fullFunctor overlapWeights (four 2) outsideObjectsClient.1 e

/-- A mixed image/outside arrow checks the actual inverse source weight in the copy formula. -/
theorem crossBoundaryArrowClient :
    adjustedValue crossBoundaryArrow = secondSwap * firstSwap := by
  have hMap : adjustedValue crossBoundaryArrow =
      SingleObj.objectAdjustmentWeight overlapInclusion overlapWeights (four 3) *
        fullValue crossBoundaryArrow *
          (SingleObj.objectAdjustmentWeight overlapInclusion overlapWeights (four 0))⁻¹ := by
    have h := SingleObj.objectAdjustment_map overlapInclusion fullFunctor overlapWeights
      crossBoundaryArrow
    exact congrArg singleObjValue h
  have hOriginal : fullValue crossBoundaryArrow =
      (secondSwap * firstSwap) * (firstSwap * secondSwap)⁻¹ := by rfl
  rw [outsideWeightClient.2, imageWeightClient.1, hOriginal] at hMap
  simpa only [one_mul, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hMap

end MathlibExtTest.SingleObjDescent

end
