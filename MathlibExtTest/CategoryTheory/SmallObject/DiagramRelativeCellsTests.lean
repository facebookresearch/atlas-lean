/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.SmallObject.DiagramRelativeCells

set_option autoImplicit false
noncomputable section

universe w t a uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace DiagramRelativeCellsTests

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
  [∀ i j : J, HasCoproductsOfShape (i ⟶ j) C]
  {α : Type a} {A B : α → C} (g : ∀ i, A i ⟶ B i) (loc : α → J)
  {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
  {X Y : J ⥤ C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun (_ : T) i =>
    (evaluationLeftAdjoint C (loc i)).map (g i)) f) (k : J)
  [PreservesColimit c.F ((evaluation J C).obj k)]
  (hLimit : ∀ j : T, Order.IsSuccLimit j → PreservesColimit
    ((Set.principalSegIio j).monotone.functor ⋙ c.F) ((evaluation J C).obj k))
  (hSource : ∀ (j : T) (hj : ¬ IsMax j), PreservesColimit
    (Discrete.functor (fun s : (c.attachCells j hj).ι =>
      (evaluationLeftAdjoint C (loc ((c.attachCells j hj).π s))).obj
        (A ((c.attachCells j hj).π s)))) ((evaluation J C).obj k))
  (hTarget : ∀ (j : T) (hj : ¬ IsMax j), PreservesColimit
    (Discrete.functor (fun s : (c.attachCells j hj).ι =>
      (evaluationLeftAdjoint C (loc ((c.attachCells j hj).π s))).obj
        (B ((c.attachCells j hj).π s)))) ((evaluation J C).obj k))
  (hPushout : ∀ (j : T) (hj : ¬ IsMax j), PreservesColimit
    (span (c.attachCells j hj).g₁ (c.attachCells j hj).m) ((evaluation J C).obj k))

-- No source-presentability, cardinal-SOA, model, or global preservation premise is supplied.
example : RelativeCellComplex.{max w vJ} (fun (_ : T) => g)
    (((evaluation J C).obj k).map f) :=
  c.evaluateFreeDiagrams g loc k hLimit hSource hTarget hPushout

example : (c.evaluateFreeDiagrams g loc k hLimit hSource hTarget hPushout).F =
    c.F ⋙ (evaluation J C).obj k :=
  c.evaluateFreeDiagrams_F g loc k hLimit hSource hTarget hPushout

example (j : T) :
    (c.evaluateFreeDiagrams g loc k hLimit hSource hTarget hPushout).incl.app j =
      (c.incl.app j).app k :=
  c.evaluateFreeDiagrams_incl g loc k hLimit hSource hTarget hPushout j

-- The endpoint colimit is the original mapped canonical cocone, not a replacement diagram.
example : IsColimit (Cocone.mk (Y.obj k)
    (c.evaluateFreeDiagrams g loc k hLimit hSource hTarget hPushout).incl) :=
  (c.evaluateFreeDiagrams g loc k hLimit hSource hTarget hPushout).isColimit

example (hSmall : ∀ (j : T) (hj : ¬ IsMax j),
    Small.{w} (Σ s : (c.attachCells j hj).ι, loc ((c.attachCells j hj).π s) ⟶ k)) :
    RelativeCellComplex.{w} (fun (_ : T) => g) (((evaluation J C).obj k).map f) :=
  c.evaluateFreeDiagramsOfSmall g loc k hLimit hSource hTarget hPushout hSmall

#check @RelativeCellComplex.evaluateFreeDiagrams
#check @RelativeCellComplex.evaluateFreeDiagrams_F
#check @RelativeCellComplex.evaluateFreeDiagrams_incl
#check @RelativeCellComplex.evaluateFreeDiagramsOfSmall
#print axioms RelativeCellComplex.evaluateFreeDiagrams
#print axioms RelativeCellComplex.evaluateFreeDiagrams_F
#print axioms RelativeCellComplex.evaluateFreeDiagrams_incl
#print axioms RelativeCellComplex.evaluateFreeDiagramsOfSmall

end DiagramRelativeCellsTests
