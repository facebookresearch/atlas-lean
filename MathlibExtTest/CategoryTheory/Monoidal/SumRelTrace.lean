/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.SumRelTrace
import MathlibExt.CategoryTheory.Monoidal.RelCat
import MathlibExt.CategoryTheory.Monoidal.IntConstruction

open CategoryTheory MonoidalCategory
open CategoryTheory.SumRelCat
universe u

-- The six axioms are available on arbitrary objects with default options.
example : SymmetricTrace SumRelCat.{u} := SumRelCat.symmetricTrace
example {X X' Y Y' U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U)
    (g : X' ⟶ X) (h : Y ⟶ Y') :
    SumRelCat.symmetricTrace.trace ((g ⊗ₘ 𝟙 U) ≫ f ≫ (h ⊗ₘ 𝟙 U)) =
      g ≫ SumRelCat.symmetricTrace.trace f ≫ h := SumRelCat.symmetricTrace.naturality f g h
example {X Y U V : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ V) (g : V ⟶ U) :
    SumRelCat.symmetricTrace.trace (f ≫ (𝟙 Y ⊗ₘ g)) =
      SumRelCat.symmetricTrace.trace ((𝟙 X ⊗ₘ g) ≫ f) :=
  SumRelCat.symmetricTrace.dinaturality f g
example {X Y : SumRelCat.{u}} (f : X ⊗ 𝟙_ SumRelCat ⟶ Y ⊗ 𝟙_ SumRelCat) :
    SumRelCat.symmetricTrace.trace f = (ρ_ X).inv ≫ f ≫ (ρ_ Y).hom :=
  SumRelCat.symmetricTrace.vanishing_unit f
example {X Y U V : SumRelCat.{u}} (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V)) :
    SumRelCat.symmetricTrace.trace f = SumRelCat.symmetricTrace.trace
      (SumRelCat.symmetricTrace.trace ((α_ X U V).hom ≫ f ≫ (α_ Y U V).inv)) :=
  SumRelCat.symmetricTrace.vanishing_tensor f
example {X Y U W Z : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) (g : W ⟶ Z) :
    SumRelCat.symmetricTrace.trace ((α_ W X U).hom ≫ (g ⊗ₘ f) ≫ (α_ Z Y U).inv) =
      g ⊗ₘ SumRelCat.symmetricTrace.trace f := SumRelCat.symmetricTrace.superposing f g
example (X : SumRelCat.{u}) : SumRelCat.symmetricTrace.trace (β_ X X).hom = 𝟙 X :=
  SumRelCat.symmetricTrace.yanking X
example {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) :
    SumRelCat.symmetricTrace.trace f = feedback f := by simp

-- The two imported trace models have different empty-feedback behavior.
example (x y : Bool) :
    (x, y) ∈ (SumRelCat.symmetricTrace.trace (𝟙 (of Bool ⊗ of PEmpty))).rel ↔ x = y := by
  have h : SumRelCat.symmetricTrace.trace (𝟙 (of Bool ⊗ of PEmpty)) = 𝟙 (of Bool) := by
    simpa using feedback_tensor (𝟙 (of Bool)) (𝟙 (of PEmpty))
  rw [h]
  rfl
example (x y : Bool) :
    (x, y) ∉ (RelCat.symmetricTrace.trace (RelCat.instLargeCategory.id (Bool × PEmpty))).rel := by
  intro h
  obtain ⟨w, _⟩ := (RelCat.trace_rel _ x y).mp h
  exact PEmpty.elim w

namespace SumRelTraceTests
private def entryOnly : of PUnit ⊗ of PUnit ⟶ of PUnit ⊗ of PUnit :=
  .ofRel {p | p.1 = Sum.inl PUnit.unit ∧ p.2 = Sum.inr PUnit.unit}
private def exitOnly : of PUnit ⊗ of PUnit ⟶ of PUnit ⊗ of PUnit :=
  .ofRel {p | p.1 = Sum.inr PUnit.unit ∧ p.2 = Sum.inl PUnit.unit}
private def joined : of PUnit ⊗ of PUnit ⟶ of PUnit ⊗ of PUnit :=
  .ofRel (entryOnly.rel ∪ exitOnly.rel)

-- The union creates a terminating path that neither relation contains separately.
example : (SumRelCat.symmetricTrace.trace entryOnly).rel = ∅ := by
  apply feedback_eq_empty_of_no_exit
  intro s y
  simp [entryOnly]
example : (SumRelCat.symmetricTrace.trace exitOnly).rel = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨x, y⟩ h
  have hx := (feedback_rel_of_no_entry exitOnly (by intro x a; simp [exitOnly]) x y).mp h
  simp [exitOnly] at hx
example : (PUnit.unit, PUnit.unit) ∈ (SumRelCat.symmetricTrace.trace joined).rel :=
  FeedbackPath.step (Or.inl ⟨rfl, rfl⟩) (.output (Or.inr ⟨rfl, rfl⟩))
example : (SumRelCat.symmetricTrace.trace joined).rel ≠
    (SumRelCat.symmetricTrace.trace entryOnly).rel ∪
      (SumRelCat.symmetricTrace.trace exitOnly).rel := by
  intro h
  have member : (PUnit.unit, PUnit.unit) ∈ (SumRelCat.symmetricTrace.trace joined).rel :=
    FeedbackPath.step (Or.inl ⟨rfl, rfl⟩) (.output (Or.inr ⟨rfl, rfl⟩))
  rw [h] at member
  rcases member with h | h
  · have noexit := feedback_eq_empty_of_no_exit entryOnly (by intro s y; simp [entryOnly])
    change (PUnit.unit, PUnit.unit) ∈ (feedback entryOnly).rel at h
    rw [noexit] at h
    exact h
  · have hx := (feedback_rel_of_no_entry exitOnly (by intro x a; simp [exitOnly]) _ _).mp h
    simp [exitOnly] at hx

private def alternating : of PUnit ⊗ (of Bool ⊗ of Bool) ⟶ of PUnit ⊗ (of Bool ⊗ of Bool) :=
  .ofRel {p | p = (Sum.inl PUnit.unit, Sum.inr (Sum.inl false)) ∨
    p = (Sum.inr (Sum.inl false), Sum.inr (Sum.inr false)) ∨
    p = (Sum.inr (Sum.inr false), Sum.inr (Sum.inl true)) ∨
    p = (Sum.inr (Sum.inl true), Sum.inr (Sum.inr true)) ∨
    p = (Sum.inr (Sum.inr true), Sum.inl PUnit.unit)}
private theorem alternating_path :
    (PUnit.unit, PUnit.unit) ∈ (feedback alternating).rel := by
  change FeedbackPath alternating (Sum.inl PUnit.unit) PUnit.unit
  refine .step (v := Sum.inl false) ?_ ?_
  · exact Or.inl rfl
  refine .step (v := Sum.inr false) ?_ ?_
  · exact Or.inr (Or.inl rfl)
  refine .step (v := Sum.inl true) ?_ ?_
  · exact Or.inr (Or.inr (Or.inl rfl))
  refine .step (v := Sum.inr true) ?_ ?_
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  exact .output (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
example : (PUnit.unit, PUnit.unit) ∈ (SumRelCat.symmetricTrace.trace alternating).rel :=
  alternating_path
example : (PUnit.unit, PUnit.unit) ∈ (SumRelCat.symmetricTrace.trace
    (SumRelCat.symmetricTrace.trace ((α_ (of PUnit) (of Bool) (of Bool)).hom ≫
      alternating ≫ (α_ (of PUnit) (of Bool) (of Bool)).inv))).rel := by
  rw [← SumRelCat.symmetricTrace.vanishing_tensor]
  exact alternating_path
end SumRelTraceTests

-- Int can consume this non-product trace without any additional rigidity assumption.
example : Category (IntConstruction SumRelCat.symmetricTrace) := inferInstance
example : (IntConstruction.embedding SumRelCat.symmetricTrace).Full := inferInstance
example : (IntConstruction.embedding SumRelCat.symmetricTrace).Faithful := inferInstance
example {X Y Z : SumRelCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (IntConstruction.embedding SumRelCat.symmetricTrace).map (f ≫ g) =
      (IntConstruction.embedding SumRelCat.symmetricTrace).map f ≫
        (IntConstruction.embedding SumRelCat.symmetricTrace).map g := by simp
