/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.SmallObject.DiagramEvaluation

set_option autoImplicit false
noncomputable section

universe w a uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace DiagramEvaluationTests

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
  [∀ i j : J, HasCoproductsOfShape (i ⟶ j) C]
  {α : Type a} {A B : α → C} (g : ∀ t, A t ⟶ B t) (loc : α → J)
  {X Y : J ⥤ C} {f : X ⟶ Y}
  (c : AttachCells.{w} (fun t => (evaluationLeftAdjoint C (loc t)).map (g t)) f)
  (k : J)
  [PreservesColimit (Discrete.functor (fun s : c.ι =>
    (evaluationLeftAdjoint C (loc (c.π s))).obj (A (c.π s)))) ((evaluation J C).obj k)]
  [PreservesColimit (Discrete.functor (fun s : c.ι =>
    (evaluationLeftAdjoint C (loc (c.π s))).obj (B (c.π s)))) ((evaluation J C).obj k)]
  [PreservesColimit (span c.g₁ c.m) ((evaluation J C).obj k)]

-- No model, source-presentability, or global colimit-preservation premise is supplied.
example : AttachCells.{max w vJ} g (((evaluation J C).obj k).map f) :=
  c.evaluateFreeDiagrams g loc k

-- The chosen source/target points and all three pushout-square maps are retained.
example : (c.evaluateFreeDiagrams g loc k).cofan₁.pt = c.cofan₁.pt.obj k := rfl
example : (c.evaluateFreeDiagrams g loc k).cofan₂.pt = c.cofan₂.pt.obj k := rfl
example : (c.evaluateFreeDiagrams g loc k).g₁ = c.g₁.app k := rfl
example : (c.evaluateFreeDiagrams g loc k).g₂ = c.g₂.app k := rfl

example (s : c.ι) (h : loc (c.π s) ⟶ k) :
    (c.evaluateFreeDiagrams g loc k).cofan₁.inj ⟨s, h⟩ =
      Sigma.ι (fun _ : loc (c.π s) ⟶ k => A (c.π s)) h ≫ (c.cofan₁.inj s).app k :=
  c.evaluateFreeDiagrams_source_generator g loc k s h

example (s : c.ι) (h : loc (c.π s) ⟶ k) :
    (c.evaluateFreeDiagrams g loc k).cofan₂.inj ⟨s, h⟩ =
      Sigma.ι (fun _ : loc (c.π s) ⟶ k => B (c.π s)) h ≫ (c.cofan₂.inj s).app k :=
  c.evaluateFreeDiagrams_target_generator g loc k s h

example : (c.evaluateFreeDiagrams g loc k).m = c.m.app k :=
  c.evaluateFreeDiagrams_map g loc k

-- The raw Hom universe need not equal w: only the actual combined cell index is small.
example [Small.{w} (Σ s : c.ι, loc (c.π s) ⟶ k)] :
    AttachCells.{w} g (((evaluation J C).obj k).map f) :=
  c.evaluateFreeDiagramsOfSmall g loc k

-- Empty cross-Hom sets yield no flattened cells, while the same square is retained.
example [∀ s : c.ι, IsEmpty (loc (c.π s) ⟶ k)] :
    IsEmpty (c.evaluateFreeDiagrams g loc k).ι :=
  ⟨fun p => isEmptyElim p.2⟩

#check @AttachCells.evaluateFreeDiagrams
#check @AttachCells.evaluateFreeDiagrams_index
#check @AttachCells.evaluateFreeDiagrams_source_generator
#check @AttachCells.evaluateFreeDiagrams_target_generator
#check @AttachCells.evaluateFreeDiagrams_map
#check @AttachCells.evaluateFreeDiagramsOfSmall
#print axioms AttachCells.evaluateFreeDiagrams
#print axioms AttachCells.evaluateFreeDiagrams_index
#print axioms AttachCells.evaluateFreeDiagrams_source_generator
#print axioms AttachCells.evaluateFreeDiagrams_target_generator
#print axioms AttachCells.evaluateFreeDiagrams_map
#print axioms AttachCells.evaluateFreeDiagramsOfSmall

end DiagramEvaluationTests
