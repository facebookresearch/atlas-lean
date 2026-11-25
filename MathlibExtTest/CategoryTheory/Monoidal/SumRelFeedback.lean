/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.SumRelFeedback
open CategoryTheory MonoidalCategory
open CategoryTheory.SumRelCat
universe u
example {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) (x : X) (y : Y)
    (h : (Sum.inl x, Sum.inl y) ∈ f.rel) : (x, y) ∈ (feedback f).rel :=
  FeedbackPath.output h

-- Abstract consumers of the closure formula, including zero internal steps.
example {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) (x : X) (y : Y) (a : U)
    (hin : (Sum.inl x, Sum.inr a) ∈ f.rel)
    (hout : (Sum.inr a, Sum.inl y) ∈ f.rel) : (x, y) ∈ (feedback f).rel :=
  FeedbackPath.step hin (.output hout)
example {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) (x : X) (y : Y) (a b : U)
    (hin : (Sum.inl x, Sum.inr a) ∈ f.rel)
    (hab : (Sum.inr a, Sum.inr b) ∈ f.rel)
    (hout : (Sum.inr b, Sum.inl y) ∈ f.rel) : (x, y) ∈ (feedback f).rel :=
  FeedbackPath.step hin (.step hab (.output hout))
example {X Y U : SumRelCat.{u}} {f g : X ⊗ U ⟶ Y ⊗ U} (h : f.rel ⊆ g.rel)
    {x : X} {y : Y} (hxy : (x, y) ∈ (feedback f).rel) :
    (x, y) ∈ (feedback g).rel := feedback_mono h hxy
example {X Y : SumRelCat.{u}} (f : X ⊗ zero ⟶ Y ⊗ zero) (x : X) (y : Y) :
    (x, y) ∈ (feedback f).rel ↔ (Sum.inl x, Sum.inl y) ∈ f.rel := feedback_zero f x y

namespace SumRelFeedbackTests

-- This relation can enter a hidden loop but has no output edge.
private def loopOnly : of PUnit ⊗ of Bool ⟶ of Bool ⊗ of Bool :=
  .ofRel {p | p.2 = Sum.inr false}
example : (feedback loopOnly).rel = ∅ := by
  apply feedback_eq_empty_of_no_exit
  intro s y
  simp [loopOnly]
example : (PUnit.unit, true) ∉ (feedback loopOnly).rel := by
  rw [feedback_eq_empty_of_no_exit loopOnly (by intro s y; simp [loopOnly])]
  simp

-- A loop with two exits retains both outputs, and it may loop before exiting.
private def branchingLoop : of PUnit ⊗ of Bool ⟶ of Bool ⊗ of Bool :=
  .ofRel {p | p.2 = Sum.inr false ∨ p.1 = Sum.inr false}
example : (PUnit.unit, false) ∈ (feedback branchingLoop).rel :=
  FeedbackPath.step (Or.inl rfl) (.output (Or.inr rfl))
example : (PUnit.unit, true) ∈ (feedback branchingLoop).rel :=
  FeedbackPath.step (Or.inl rfl) (.output (Or.inr rfl))
example : (PUnit.unit, true) ∈ (feedback branchingLoop).rel :=
  FeedbackPath.step (Or.inl rfl) (.step (Or.inl rfl) (.output (Or.inr rfl)))

-- The hidden carrier is infinite and paths of arbitrary finite length are supported.
private def chain (n : ℕ) : of PUnit ⊗ of ℕ ⟶ of PUnit ⊗ of ℕ :=
  .ofRel {p | match p.1, p.2 with
    | .inl _, .inr b => b = 0
    | .inr a, .inr b => b = a + 1
    | .inr a, .inl _ => a = n
    | _, _ => False}
example (n : ℕ) : (PUnit.unit, PUnit.unit) ∈ (feedback (chain n)).rel := by
  rw [feedback_rel]
  right
  refine ⟨0, n, rfl, ?_, rfl⟩
  have path (k : ℕ) : Relation.ReflTransGen
      (fun a b : ℕ => (Sum.inr a, Sum.inr b) ∈ (chain n).rel) 0 k := by
    induction k with
    | zero => exact .refl
    | succ k ih => exact ih.tail rfl
  exact path n

-- No direct input/output edge is needed: this example needs two hidden transitions.
example : (PUnit.unit, PUnit.unit) ∈ (feedback (chain 2)).rel :=
  FeedbackPath.step rfl (.step rfl (.step rfl (.output rfl)))

example (X : SumRelCat.{u}) : feedback (𝟙 (X ⊗ of PEmpty)) = 𝟙 X := by
  apply Hom.ext
  ext ⟨x, y⟩
  rw [feedback_zero]
  simp [rel_id, SetRel.id]

-- Least-solution reasoning uses an invariant on the input-or-feedback states.
example {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) (P : Sum X U → Y → Prop)
    (hout : ∀ s y, (s, Sum.inl y) ∈ f.rel → P s y)
    (hstep : ∀ s a y, (s, Sum.inr a) ∈ f.rel → P (Sum.inr a) y → P s y)
    (x : X) (y : Y) (hxy : (x, y) ∈ (feedback f).rel) : P (Sum.inl x) y :=
  FeedbackPath.least hout hstep hxy
end SumRelFeedbackTests

-- A disjoint closed subsystem cannot change the visible relation.
example {X Y U : SumRelCat.{u}} (f : X ⟶ Y) (g : U ⟶ U) :
    feedback (f ⊗ₘ g) = f := by simp
example (X U : SumRelCat.{u}) : feedback (𝟙 (X ⊗ U)) = 𝟙 X := by
  simpa using feedback_tensor (𝟙 X) (𝟙 U)
