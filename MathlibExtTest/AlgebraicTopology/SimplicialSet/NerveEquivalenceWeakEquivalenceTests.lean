/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

import Mathlib.CategoryTheory.IsConnected

/-!
# Tests for nerve equivalences and initial-object contractions

These tests cover the identity equivalence, a genuinely non-strict
equivalence, the two homotopy orientations, an explicit initial object,
ordinary and mixed universes, standard axioms, and negative nonclaims.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits NerveContractible
open scoped Simplicial

universe v u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace NerveEquivalenceWeakEquivalenceTests

section Identity

variable {C : Type u} [Category.{v} C]

example : SSet.realizationWeakEquivalences
    (CategoryTheory.nerveMap (𝟭 C)) :=
  CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence
    (𝟭 C)

end Identity

section HomotopyOrientations

variable {A B : Type u} [Category.{v} A] [Category.{v} B]

example (E : A ≌ B) : SSet.Homotopy
    (CategoryTheory.nerveMap E.functor ≫
      CategoryTheory.nerveMap E.inverse)
    (𝟙 (CategoryTheory.nerve A : SSet.{max u v})) := by
  simpa only [CategoryTheory.nerveMap_comp,
    CategoryTheory.nerveMap_id] using
      (CategoryTheory.NatTrans.nerveHomotopy E.unitInv)

example (E : A ≌ B) : SSet.Homotopy
    (CategoryTheory.nerveMap E.inverse ≫
      CategoryTheory.nerveMap E.functor)
    (𝟙 (CategoryTheory.nerve B : SSet.{max u v})) := by
  simpa only [CategoryTheory.nerveMap_comp,
    CategoryTheory.nerveMap_id] using
      (CategoryTheory.NatTrans.nerveHomotopy E.counit)

end HomotopyOrientations

private inductive ContractiblePair
  | left
  | right
  deriving DecidableEq

private inductive ContractiblePoint
  | star
  deriving DecidableEq

private instance contractiblePairCategory : Category ContractiblePair where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

private instance contractiblePointCategory : Category ContractiblePoint where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

private def pairToPoint : ContractiblePair ⥤ ContractiblePoint where
  obj _ := .star
  map _ := PUnit.unit
  map_id _ := rfl
  map_comp _ _ := rfl

private def pointToPair : ContractiblePoint ⥤ ContractiblePair where
  obj _ := .left
  map _ := PUnit.unit
  map_id _ := rfl
  map_comp _ _ := rfl

private def pairUniqueIso (X Y : ContractiblePair) : X ≅ Y where
  hom := PUnit.unit
  inv := PUnit.unit

private def pairUnitIso : 𝟭 ContractiblePair ≅ pairToPoint ⋙ pointToPair :=
  NatIso.ofComponents (fun X => pairUniqueIso X .left)

private def pointCounitIso : pointToPair ⋙ pairToPoint ≅ 𝟭 ContractiblePoint :=
  NatIso.ofComponents (fun _ => Iso.refl _)

private noncomputable def pairPointEquivalence :
    ContractiblePair ≌ ContractiblePoint :=
  CategoryTheory.Equivalence.mk
    pairToPoint pointToPair pairUnitIso pointCounitIso

private def contractiblePairLeftIsInitial :
    IsInitial ContractiblePair.left :=
  IsInitial.ofUniqueHom (fun _ => PUnit.unit) (by
    intro Y f
    rfl)

section NontrivialEquivalence

example : ¬ Function.Injective pairPointEquivalence.functor.obj := by
  intro h
  have hne : ContractiblePair.left ≠ ContractiblePair.right := by decide
  exact hne (h rfl)

example : SSet.realizationWeakEquivalences
    (CategoryTheory.nerveMap pairPointEquivalence.functor) :=
  CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence
    pairPointEquivalence.functor

end NontrivialEquivalence

section InitialObject

example : SSet.realizationWeakEquivalences
    (terminal.from (CategoryTheory.nerve ContractiblePair)) :=
  terminal_from_mem_realizationWeakEquivalences_of_isInitial
    contractiblePairLeftIsInitial

example : SSet.Homotopy
    (NerveContractible.constNerveMap ContractiblePair.left)
    (𝟙 (CategoryTheory.nerve ContractiblePair)) := by
  let η : (Functor.const ContractiblePair).obj ContractiblePair.left ⟶
      𝟭 ContractiblePair :=
    { app := fun _ => PUnit.unit }
  simpa only [NerveContractible.constNerveMap,
    CategoryTheory.nerveMap_id] using
      (CategoryTheory.NatTrans.nerveHomotopy η)

end InitialObject

section Universes

variable {C₀₀ : Type} [Category C₀₀]
variable {C₁₁ : Type 1} [Category.{1} C₁₁]
variable {C₀₁ : Type} [Category.{1} C₀₁]
variable {C₁₀ : Type 1} [Category.{0} C₁₀]

example : SSet.realizationWeakEquivalences
    (CategoryTheory.nerveMap (𝟭 C₀₀)) :=
  CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence
    (𝟭 C₀₀)

example : SSet.realizationWeakEquivalences
    (CategoryTheory.nerveMap (𝟭 C₁₁)) :=
  CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence
    (𝟭 C₁₁)

example : SSet.realizationWeakEquivalences
    (CategoryTheory.nerveMap (𝟭 C₀₁)) :=
  CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence
    (𝟭 C₀₁)

example : SSet.realizationWeakEquivalences
    (CategoryTheory.nerveMap (𝟭 C₁₀)) :=
  CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence
    (𝟭 C₁₀)

example {X : C₀₀} (hX : IsInitial X) :
    SSet.realizationWeakEquivalences
      (terminal.from (CategoryTheory.nerve C₀₀)) :=
  terminal_from_mem_realizationWeakEquivalences_of_isInitial hX

example {X : C₁₁} (hX : IsInitial X) :
    SSet.realizationWeakEquivalences
      (terminal.from (CategoryTheory.nerve C₁₁)) :=
  terminal_from_mem_realizationWeakEquivalences_of_isInitial hX

example {X : C₀₁} (hX : IsInitial X) :
    SSet.realizationWeakEquivalences
      (terminal.from (CategoryTheory.nerve C₀₁)) :=
  terminal_from_mem_realizationWeakEquivalences_of_isInitial hX

example {X : C₁₀} (hX : IsInitial X) :
    SSet.realizationWeakEquivalences
      (terminal.from (CategoryTheory.nerve C₁₀)) :=
  terminal_from_mem_realizationWeakEquivalences_of_isInitial hX

end Universes

/- An equivalence of categories need not induce an isomorphism of nerves. -/
#guard_msgs (error, substring := true) in
example {A B : Type} [Category A] [Category B]
    (F : A ⥤ B) [F.IsEquivalence] :
    IsIso (CategoryTheory.nerveMap F) := by
  infer_instance

/- Connectedness alone does not supply an initial-object contraction. -/
#guard_msgs (error, substring := true) in
example {C : Type} [Category C] [IsConnected C] :
    SSet.realizationWeakEquivalences
      (terminal.from (CategoryTheory.nerve C)) := by
  apply terminal_from_mem_realizationWeakEquivalences_of_isInitial

#print axioms CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence
#print axioms NerveContractible.terminal_from_mem_realizationWeakEquivalences_of_isInitial

end NerveEquivalenceWeakEquivalenceTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
