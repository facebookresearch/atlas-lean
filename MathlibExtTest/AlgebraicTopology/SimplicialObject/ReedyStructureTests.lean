/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyFibrantObjects
public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyComponentCofibrations
public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyPresheafMonomorphisms
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# The Reedy structure of simplicial objects in examples

The Reedy structure of `SimplexCategoryᵒᵖ` has the expected degrees, direct and inverse maps; the
latching and matching indices are finite categories, so Reedy factorizations exist in every
category with finite limits and colimits; and on the category of types with the model structure
whose cofibrations and fibrations are all maps and whose weak equivalences are the bijections, the
Reedy model structure on simplicial types is exercised on the collapse `Bool → PUnit` of constant
simplicial types, on bisimplicial monomorphisms, and on the proper degeneracies and faces of `⦋1⦌`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Opposite
open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject.ReedyStructureTests

/-! ### The Reedy structure of `SimplexCategoryᵒᵖ` -/

example : reedyStructure.degree (op ⦋3⦌) = 3 := rfl

example : reedyStructure.direct (SimplexCategory.σ (0 : Fin 1)).op :=
  (reedyStructure_direct_iff _).2 inferInstance

example : reedyStructure.inverse (SimplexCategory.δ (0 : Fin 2)).op :=
  (reedyStructure_inverse_iff _).2 inferInstance

/-- A face map is not a direct map. -/
example : ¬ reedyStructure.direct (SimplexCategory.δ (0 : Fin 2)).op := by
  rw [reedyStructure_direct_iff]
  intro h
  have := @SimplexCategory.len_le_of_epi _ _ (SimplexCategory.δ (0 : Fin 2)) h
  exact absurd this (by decide)

/-! ### Finite latching and matching indices -/

example : FinCategory (latchingIndex 2) := inferInstance

example : FinCategory (matchingIndex 2) := inferInstance

section Finite

variable {C : Type u} [Category.{v} C]

example (n : ℕ) [HasFiniteColimits C] : HasColimitsOfShape (latchingIndex n) C :=
  inferInstance

example (n : ℕ) [HasFiniteLimits C] : HasLimitsOfShape (matchingIndex n) C :=
  inferInstance

/-- Reedy factorizations only need finite limits and colimits. -/
example [HasFiniteColimits C] [HasFiniteLimits C] {X Y : SimplicialObject C} (f : X ⟶ Y)
    (P Q : MorphismProperty C) [P.HasFactorization Q] [P.RespectsIso] [Q.RespectsIso] :
    (reedyLeft P).MapFactorizationData (reedyRight Q) f :=
  reedyMapFactorizationData f P Q

/-- Under the latching equivalence, the generic latching map is the simplicial one. -/
example [HasFiniteColimits C] (X : SimplicialObject C) (n : ℕ) :
    reedyStructure.latchingMap X (op ⦋n⦌) = (latchingObjectIso X n).hom ≫ latchingMap X n :=
  reedyStructure_latchingMap_eq X n

end Finite

/-! ### A model structure on types -/

/-- The model structure on a finitely complete and cocomplete category whose cofibrations and
fibrations are all maps and whose weak equivalences are the isomorphisms. -/
@[instance_reducible]
def discreteModel (C : Type u) [Category.{v} C]
    [HasFiniteLimits C] [HasFiniteColimits C] : ModelCategory C := by
  letI : CategoryWithCofibrations C := ⟨⊤⟩
  letI : CategoryWithFibrations C := ⟨⊤⟩
  letI : CategoryWithWeakEquivalences C := ⟨isomorphisms C⟩
  let _ : (cofibrations C).IsStableUnderRetracts := by
    change (⊤ : MorphismProperty C).IsStableUnderRetracts
    exact ⟨fun _ _ => trivial⟩
  let _ : (fibrations C).IsStableUnderRetracts := by
    change (⊤ : MorphismProperty C).IsStableUnderRetracts
    exact ⟨fun _ _ => trivial⟩
  let _ : (weakEquivalences C).IsStableUnderRetracts := by
    change (isomorphisms C).IsStableUnderRetracts
    infer_instance
  let _ : (weakEquivalences C).HasTwoOutOfThreeProperty := by
    change (isomorphisms C).HasTwoOutOfThreeProperty
    infer_instance
  let _ : HasFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨fun {X Y} f => ⟨{
      Z := X
      i := 𝟙 X
      p := f
      fac := by simp
      hi := ⟨trivial, (show IsIso (𝟙 X) from inferInstance)⟩
      hp := trivial }⟩⟩
  let _ : HasFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨fun {X Y} f => ⟨{
      Z := Y
      i := f
      p := 𝟙 Y
      fac := by simp
      hi := trivial
      hp := ⟨trivial, (show IsIso (𝟙 Y) from inferInstance)⟩ }⟩⟩
  let _ : IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C) :=
    IsWeakFactorizationSystem.mk' _ _ (fun i p hi _ => by
      let _ : IsIso i := hi.2
      infer_instance)
  let _ : IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C) :=
    IsWeakFactorizationSystem.mk' _ _ (fun i p _ hp => by
      let _ : IsIso p := hp.2
      infer_instance)
  exact ModelCategory.mk' C

local instance : ModelCategory (Type) := discreteModel (Type)

example : ModelCategory (SimplicialObject (Type)) := reedyModelCategory

open scoped CategoryTheory.SimplicialObject.reedyModelCategory

/-- The collapse `Bool → PUnit`. -/
abbrev collapse : Bool ⟶ PUnit := TypeCat.ofHom (fun _ => PUnit.unit)

/-- The constant simplicial type on `Bool`. -/
abbrev constantBool : SimplicialObject (Type) := (Functor.const SimplexCategoryᵒᵖ).obj Bool

/-- The constant simplicial type on `PUnit`. -/
abbrev constantUnit : SimplicialObject (Type) := (Functor.const SimplexCategoryᵒᵖ).obj PUnit

/-- The constant collapse map. -/
abbrev constantCollapse : constantBool ⟶ constantUnit :=
  (Functor.const SimplexCategoryᵒᵖ).map collapse

example : Cofibration constantCollapse := ⟨fun _ => trivial⟩

example : Fibration constantCollapse := ⟨fun _ => trivial⟩

/-- The collapse is not a weak equivalence: the weak equivalences are not all maps. -/
example : ¬ WeakEquivalence constantCollapse := by
  intro h
  have hzero : IsIso collapse := (weakEquivalence_iff constantCollapse).mp h (op ⦋0⦌)
  have hinjective : Function.Injective collapse := injective_of_mono collapse
  have hfalse : (false : Bool) = true := hinjective rfl
  cases hfalse

/-- The factorization of the collapse into a cofibration and a trivial fibration. -/
def cofibrationTrivialFibration :=
  factorizationData (cofibrations (SimplicialObject (Type)))
    (trivialFibrations (SimplicialObject (Type))) constantCollapse

/-- The factorization of the collapse into a trivial cofibration and a fibration. -/
def trivialCofibrationFibration :=
  factorizationData (trivialCofibrations (SimplicialObject (Type)))
    (fibrations (SimplicialObject (Type))) constantCollapse

example : cofibrationTrivialFibration.i ≫ cofibrationTrivialFibration.p = constantCollapse :=
  cofibrationTrivialFibration.fac

example : trivialCofibrationFibration.i ≫ trivialCofibrationFibration.p = constantCollapse :=
  trivialCofibrationFibration.fac

example (n : ℕ) : IsIso (cofibrationTrivialFibration.p.app (op ⦋n⦌)) :=
  cofibrationTrivialFibration.hp.2 (op ⦋n⦌)

example (n : ℕ) : IsIso (trivialCofibrationFibration.i.app (op ⦋n⦌)) :=
  trivialCofibrationFibration.hi.2 (op ⦋n⦌)

example : IsFibrant constantBool :=
  (reedyModelCategory.isFibrant_iff_matchingMaps constantBool).mpr (fun _ => trivial)

example : IsCofibrant constantBool :=
  (reedyModelCategory.isCofibrant_iff_latchingMapsIn constantBool).mpr (fun _ => trivial)

/-- Reedy cofibrations are degreewise cofibrations. -/
example : cofibrations (Type) (constantCollapse.app (op ⦋1⦌)) :=
  component_cofibration_of_reedyLeft constantCollapse (fun _ => trivial) 1

/-! ### Reedy monomorphisms of bisimplicial sets -/

/-- The empty simplicial set. -/
abbrev emptySSet : SSet := (Functor.const SimplexCategoryᵒᵖ).obj Empty

/-- The terminal simplicial set. -/
abbrev unitSSet : SSet := (Functor.const SimplexCategoryᵒᵖ).obj PUnit

/-- The inclusion of the empty simplicial set. -/
abbrev inclusion : emptySSet ⟶ unitSSet :=
  (Functor.const SimplexCategoryᵒᵖ).map (TypeCat.ofHom (fun value : Empty => nomatch value))

/-- The constant bisimplicial inclusion. -/
abbrev outerInclusion :
    (Functor.const SimplexCategoryᵒᵖ).obj emptySSet ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj unitSSet :=
  (Functor.const SimplexCategoryᵒᵖ).map inclusion

instance : Mono inclusion := by
  let _ : ∀ degree : SimplexCategoryᵒᵖ, Mono (inclusion.app degree) := fun _ => by
    apply (mono_iff_injective _).mpr
    intro value
    cases value
  exact NatTrans.mono_of_mono_app inclusion

instance : Mono outerInclusion := by
  let _ : ∀ degree : SimplexCategoryᵒᵖ, Mono (outerInclusion.app degree) := fun _ => by
    change Mono inclusion
    infer_instance
  exact NatTrans.mono_of_mono_app outerInclusion

theorem reedyLeft_outerInclusion : reedyLeft (monomorphisms SSet) outerInclusion := by
  rw [reedyLeft_monomorphisms_eq]
  exact inferInstance

example : Mono (relativeLatchingMap outerInclusion 0) := reedyLeft_outerInclusion 0

example : Mono (relativeLatchingMap outerInclusion 1) := reedyLeft_outerInclusion 1

/-! ### Latching and matching indices of `⦋1⦌` -/

/-- The degeneracy `⦋1⦌ ⟶ ⦋0⦌` as a latching index. -/
def degeneracyIndex : latchingIndex 1 :=
  ⟨CostructuredArrow.mk ((SimplexCategory.σ (0 : Fin 1)).op),
    (show Epi (SimplexCategory.σ (0 : Fin 1)) from inferInstance), by decide⟩

/-- The face `⦋0⦌ ⟶ ⦋1⦌` skipping `0`, as a matching index. -/
def firstFaceIndex : matchingIndex 1 :=
  ⟨StructuredArrow.mk ((SimplexCategory.δ (0 : Fin 2)).op),
    (show Mono (SimplexCategory.δ (0 : Fin 2)) from inferInstance), by decide⟩

/-- The face `⦋0⦌ ⟶ ⦋1⦌` skipping `1`, as a matching index. -/
def secondFaceIndex : matchingIndex 1 :=
  ⟨StructuredArrow.mk ((SimplexCategory.δ (1 : Fin 2)).op),
    (show Mono (SimplexCategory.δ (1 : Fin 2)) from inferInstance), by decide⟩

example : IsEmpty (latchingIndex 0) :=
  ⟨fun entry => (Nat.not_lt_zero _ entry.property.2).elim⟩

example : IsEmpty (matchingIndex 0) :=
  ⟨fun entry => (Nat.not_lt_zero _ entry.property.2).elim⟩

example : firstFaceIndex ≠ secondFaceIndex := by
  intro h
  have hh := congrArg (fun entry => entry.obj.hom.unop.toOrderHom 0) h
  change (1 : Fin 2) = 0 at hh
  exact (by decide : (1 : Fin 2) ≠ 0) hh

/-- The generic latching category of `op ⦋1⦌` contains the degeneracy. -/
example : reedyStructure.Latching (op ⦋1⦌) := (reedyOfLatchingIndex 1).obj degeneracyIndex

example (X : SimplicialObject (Type)) : latchingObject X 0 ≅ ⊥_ (Type) :=
  latchingObjectZeroIso X

example (X : SimplicialObject (Type)) : matchingObject X 0 ≅ ⊤_ (Type) :=
  matchingObjectZeroIso X

end CategoryTheory.SimplicialObject.ReedyStructureTests
