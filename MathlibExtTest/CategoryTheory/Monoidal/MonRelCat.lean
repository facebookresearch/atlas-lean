/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.MonRelCat
import MathlibExt.CategoryTheory.Monoidal.RelCat
import MathlibExt.CategoryTheory.Monoidal.IntConstruction

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe u
namespace MonRelCatTests
open MonRelCat

example : Category MonRelCat.{u} := inferInstance
example : MonoidalCategory MonRelCat.{u} := inferInstance
example : SymmetricCategory MonRelCat.{u} := inferInstance
example : SymmetricTrace MonRelCat.{u} := symmetricTrace

-- Identity is order, including strict upward steps, and retains its direction.
example : (0, 1) ∈ (𝟙 (of ℕ) : of ℕ ⟶ of ℕ).rel := by simp
example : (1, 0) ∉ (𝟙 (of ℕ) : of ℕ ⟶ of ℕ).rel := by simp
example : (0, 1) ∉ (RelCat.instLargeCategory.id ℕ).rel := by
  change (0 : ℕ) ≠ 1
  decide

example {X Y : MonRelCat.{u}} (f : X ⟶ Y) {x x' : X} {y y' : Y}
    (hx : x' ≤ x) (hy : y ≤ y') (h : (x, y) ∈ f.rel) : (x', y') ∈ f.rel :=
  f.closed hx hy h

private def succMap : ℕ →o ℕ := ⟨Nat.succ, fun _ _ h => Nat.succ_le_succ h⟩
example : (2, 4) ∈ (graph (X := of ℕ) (Y := of ℕ) succMap).rel := by change 3 ≤ 4; decide
example : (2, 2) ∉ (graph (X := of ℕ) (Y := of ℕ) succMap).rel := by change ¬ 3 ≤ 2; decide
example : graph (X := of ℕ) (Y := of ℕ) succMap ≫ graph (X := of ℕ) (Y := of ℕ) succMap =
    graph (X := of ℕ) (Y := of ℕ) (succMap.comp succMap) := graph_comp _ _
example : graphFunctor.map (𝟙 (Preord.of ℕ)) = 𝟙 (of ℕ) := graphFunctor.map_id _
example {A B C : Preord.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    graphFunctor.map (f ≫ g) = graphFunctor.map f ≫ graphFunctor.map g :=
  graphFunctor.map_comp _ _

-- Structural maps expose their relation under default elaboration options.
example {X Y U V : MonRelCat.{u}} (f : X ⟶ Y) (g : U ⟶ V)
    (x : X) (u : U) (y : Y) (v : V) :
    ((x, u), (y, v)) ∈ (f ⊗ₘ g).rel ↔ (x, y) ∈ f.rel ∧ (u, v) ∈ g.rel := by simp
example {X Y : MonRelCat.{u}} (x x' : X) (y y' : Y) :
    ((x, y), (y', x')) ∈ (β_ X Y).hom.rel ↔ y ≤ y' ∧ x ≤ x' := by simp
example {X Y Z : MonRelCat.{u}} (x x' : X) (y y' : Y) (z z' : Z) :
    (((x, y), z), (x', (y', z'))) ∈ (α_ X Y Z).hom.rel ↔
      x ≤ x' ∧ y ≤ y' ∧ z ≤ z' := by simp
example {X : MonRelCat.{u}} (x y : X) :
    ((PUnit.unit, x), y) ∈ (λ_ X).hom.rel ↔ x ≤ y := by simp
example {X : MonRelCat.{u}} (x y : X) :
    (x, (y, PUnit.unit)) ∈ (ρ_ X).inv.rel ↔ x ≤ y := by simp

-- A genuine preorder: distinct elements can be mutually below one another.
private def indiscrete : MonRelCat where
  carrier := Bool
  str := { le := fun _ _ => True
           lt := fun _ _ => False
           lt_iff_le_not_ge := by intros; simp
           le_refl := fun _ => trivial
           le_trans := fun _ _ _ _ _ => trivial }
example : (false, true) ∈ (𝟙 indiscrete : indiscrete ⟶ indiscrete).rel := trivial
example : (true, false) ∈ (𝟙 indiscrete : indiscrete ⟶ indiscrete).rel := trivial
example : (false, true) ∈ (symmetricTrace.trace (β_ indiscrete indiscrete).hom).rel := by
  rw [symmetricTrace.yanking]
  trivial

-- Empty feedback gives no outputs; an infinite inhabited feedback type suffices.
example (x y : ℕ) :
    (x, y) ∈ (symmetricTrace.trace (𝟙 (of ℕ ⊗ of ℕ))).rel ↔ x ≤ y := by
  change (∃ n : ℕ, x ≤ y ∧ n ≤ n) ↔ x ≤ y
  simp
example (x y : ℕ) :
    (x, y) ∉ (symmetricTrace.trace (𝟙 (of ℕ ⊗ of PEmpty))).rel := by
  rintro ⟨e, _⟩
  exact e.elim

private def total (X Y : MonRelCat.{u}) : X ⟶ Y where
  rel := Set.univ
  closed _ _ _ := trivial
example (x y : ℕ) : (x, y) ∈ (symmetricTrace.trace
    (total (of ℕ ⊗ of ℕ) (of ℕ ⊗ of ℕ))).rel := ⟨0, trivial⟩
example (x y : ℕ) : (x, y) ∉ (symmetricTrace.trace
    (total (of ℕ ⊗ of PEmpty) (of ℕ ⊗ of PEmpty))).rel := by
  rintro ⟨e, _⟩
  exact e.elim

variable {X X' Y Y' U V W Z : MonRelCat.{u}}
example (f : X ⊗ U ⟶ Y ⊗ U) (g : X' ⟶ X) (h : Y ⟶ Y') :
    symmetricTrace.trace ((g ⊗ₘ 𝟙 U) ≫ f ≫ (h ⊗ₘ 𝟙 U)) =
      g ≫ symmetricTrace.trace f ≫ h := symmetricTrace.naturality _ _ _
example (f : X ⊗ U ⟶ Y ⊗ V) (g : V ⟶ U) :
    symmetricTrace.trace (f ≫ (𝟙 Y ⊗ₘ g)) =
      symmetricTrace.trace ((𝟙 X ⊗ₘ g) ≫ f) := symmetricTrace.dinaturality _ _
example (f : X ⊗ 𝟙_ MonRelCat ⟶ Y ⊗ 𝟙_ MonRelCat) :
    symmetricTrace.trace f = (ρ_ X).inv ≫ f ≫ (ρ_ Y).hom := symmetricTrace.vanishing_unit _
example (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V)) :
    symmetricTrace.trace f = symmetricTrace.trace
      (symmetricTrace.trace ((α_ X U V).hom ≫ f ≫ (α_ Y U V).inv)) :=
  symmetricTrace.vanishing_tensor _
example (f : X ⊗ U ⟶ Y ⊗ U) (g : W ⟶ Z) :
    symmetricTrace.trace ((α_ W X U).hom ≫ (g ⊗ₘ f) ≫ (α_ Z Y U).inv) =
      g ⊗ₘ symmetricTrace.trace f := symmetricTrace.superposing _ _
example (X : MonRelCat.{u}) : symmetricTrace.trace (β_ X X).hom = 𝟙 X :=
  symmetricTrace.yanking _

example : Category (IntConstruction symmetricTrace.{u}) := inferInstance

#print axioms CategoryTheory.MonRelCat.symmetricTrace
#print axioms CategoryTheory.MonRelCat.graphFunctor
end MonRelCatTests
