/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.PowersetPrecondition

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
open CategoryTheory.PowersetVerification
universe u
namespace PowersetPreconditionTests

private def branching : SumRelCat.of Bool ⟶ SumRelCat.of Bool := .ofRel Set.univ
private def noOutputs : SumRelCat.of Bool ⟶ SumRelCat.of Bool := .ofRel ∅

-- All possible outcomes must satisfy the postcondition.
example : false ∉ liberalPre branching {false} := by
  intro h
  have bad : true ∈ ({false} : Set Bool) := h trivial
  simp at bad

-- Missing outputs impose no termination obligation.
example : liberalPre noOutputs ∅ = Set.univ := by
  ext x
  simp [liberalPre, noOutputs, SetRel.core]

example {X Y : SumRelCat.{u}} (f : X ⟶ Y) (P : Set X) (Q : Set Y) :
    directImage f P ⊆ Q ↔ P ⊆ liberalPre f Q := image_liberalPre_gc f P Q

example {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) (Q : Set Y) :
    safeInvariant f Q = (feedbackStep f Q).gfp := safeInvariant_eq_gfp f Q

example {X Y Z : SumRelCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (Q : Set Z) :
    liberalPre (f ≫ g) Q = liberalPre f (liberalPre g Q) := by
  rw [liberalPre_comp]
  rfl

example (X : SumRelCat.{u}) (Q : Set X) : liberalPre (𝟙 X) Q = Q := by simp

example {X Y U V : SumRelCat.{u}} (f : X ⟶ Y) (g : U ⟶ V) (Q : Set Y) (R : Set V) :
    liberalPre (f ⊗ₘ g) (tensorOrderIso Y V (Q, R)) =
      tensorOrderIso X U (liberalPre f Q, liberalPre g R) := liberalPre_tensor f g (Q, R)

example {X Y : SumRelCat.{u}} (f : X ⟶ Y) (P Q : Set Y) :
    liberalPre f (P ∩ Q) = liberalPre f P ∩ liberalPre f Q := liberalPre_inter f P Q

example {X Y : SumRelCat.{u}} (f : X ⟶ Y) (P : Set X) (Q : Set Y) :
    (P, Q) ∈ (verification.map f).rel ↔ P ⊆ liberalPre f Q :=
  map_rel_iff_subset_liberalPre f P Q

-- A nondeterministic relation need not preserve unions of postconditions.
example : liberalPre branching ({false} ∪ {true}) ≠
    liberalPre branching {false} ∪ liberalPre branching {true} := by
  intro h
  have hall : false ∈ liberalPre branching ({false} ∪ {true}) := by
    intro b _
    cases b <;> simp
  rw [h] at hall
  rcases hall with h | h
  · have bad : true ∈ ({false} : Set Bool) := h trivial
    simp at bad
  · have bad : false ∈ ({true} : Set Bool) := h trivial
    simp at bad

-- Arbitrarily long feedback paths over an infinite hidden carrier.
private def countdown : SumRelCat.of ℕ ⊗ SumRelCat.of ℕ ⟶
    SumRelCat.of ℕ ⊗ SumRelCat.of ℕ := .ofRel {p |
  match p.1, p.2 with
  | .inl n, .inr m => n = m
  | .inr n, .inl y => n = 0 ∧ y = 0
  | .inr n, .inr m => n = m + 1
  | _, _ => False}

private theorem countdown_path (n : ℕ) :
    SumRelCat.FeedbackPath countdown (Sum.inr n) 0 := by
  induction n with
  | zero => exact .output ⟨rfl, rfl⟩
  | succ n ih => exact .step rfl ih

example : (feedbackStep countdown {(0 : ℕ)}).gfp = Set.univ := by
  apply le_antisymm (Set.subset_univ _)
  apply OrderHom.le_gfp
  intro n _ t ht
  cases t with
  | inl y => exact (tensorOrderIso_inl _ _ _ _).mpr ht.2
  | inr m => exact (tensorOrderIso_inr _ _ _ _).mpr trivial

example : (feedbackStep countdown (∅ : Set ℕ)).gfp = ∅ := by
  rw [← safeInvariant_eq_gfp]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro n h
  exact h 0 (countdown_path n)

example (n : ℕ) : n ∉ liberalPre (SumRelCat.feedback countdown) ∅ := by
  intro h
  exact h (SumRelCat.FeedbackPath.step rfl (countdown_path n))

-- Every fixed point is safe; post-fixed points are already enough.
example {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) (Q : Set Y) (I : Set U)
    (hI : I ⊆ feedbackStep f Q I) : I ⊆ safeInvariant f Q := subset_safeInvariant f Q I hI

-- Pure divergence distinguishes the greatest fixed point from the least one.
private def spin : SumRelCat.of Bool ⊗ SumRelCat.of Bool ⟶
    SumRelCat.of Bool ⊗ SumRelCat.of Bool := .ofRel {p |
  p.2 = Sum.inr (Sum.elim id id p.1)}

private theorem spin_step : feedbackStep spin ∅ = OrderHom.id := by
  ext I b
  cases b <;> simp [feedbackStep, liberalPre, spin, SetRel.core, tensorOrderIso]

private theorem spin_gfp : (feedbackStep spin ∅).gfp = Set.univ := by
  apply le_antisymm (Set.subset_univ _)
  apply OrderHom.le_gfp
  rw [spin_step]
  exact le_rfl

example : (feedbackStep spin ∅).gfp = Set.univ := spin_gfp

example : liberalPre (SumRelCat.feedback spin) ∅ = Set.univ := by
  rw [liberalPre_feedback, spin_gfp]
  ext b
  constructor
  · exact fun _ => trivial
  · intro _ t ht
    change t = Sum.inr b at ht
    subst t
    exact (tensorOrderIso_inr _ _ _ _).mpr trivial

-- Empty external and feedback carriers require no nonemptiness hypothesis.
example : liberalPre (𝟙 (SumRelCat.of PEmpty.{u + 1})) ∅ = ∅ := by simp

#print axioms safeInvariant_eq_gfp
#print axioms liberalPre_feedback
end PowersetPreconditionTests
