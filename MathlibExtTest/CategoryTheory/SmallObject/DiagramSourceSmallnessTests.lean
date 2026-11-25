/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.SmallObject.DiagramSourceSmallness

set_option autoImplicit false
noncomputable section

universe w a uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite

namespace DiagramSourceSmallnessTests

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
  [∀ i j : J, HasCoproductsOfShape (i ⟶ j) C]
  (κ : Cardinal.{w}) [OrderBot κ.ord.ToType]
  {α : Type a} {A B : α → C} (g : ∀ i, A i ⟶ B i) (loc : α → J)
  {X Y : J ⥤ C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) i =>
    (evaluationLeftAdjoint C (loc i)).map (g i)) f) (k : J)
  [PreservesColimit c.F ((evaluation J C).obj k)]
  (hLimit : ∀ j : κ.ord.ToType, Order.IsSuccLimit j → PreservesColimit
    ((Set.principalSegIio j).monotone.functor ⋙ c.F) ((evaluation J C).obj k))
  (hSource : ∀ (j : κ.ord.ToType) (hj : ¬ IsMax j), PreservesColimit
    (Discrete.functor (fun s : (c.attachCells j hj).ι =>
      (evaluationLeftAdjoint C (loc ((c.attachCells j hj).π s))).obj
        (A ((c.attachCells j hj).π s)))) ((evaluation J C).obj k))
  (hTarget : ∀ (j : κ.ord.ToType) (hj : ¬ IsMax j), PreservesColimit
    (Discrete.functor (fun s : (c.attachCells j hj).ι =>
      (evaluationLeftAdjoint C (loc ((c.attachCells j hj).π s))).obj
        (B ((c.attachCells j hj).π s)))) ((evaluation J C).obj k))
  (hPushout : ∀ (j : κ.ord.ToType) (hj : ¬ IsMax j), PreservesColimit
    (span (c.attachCells j hj).g₁ (c.attachCells j hj).m) ((evaluation J C).obj k))
  (P : MorphismProperty C) (hg : ∀ i, P (g i))
  (hSmall : ∀ (j : κ.ord.ToType) (hj : ¬ IsMax j),
    Small.{w} (Σ s : (c.attachCells j hj).ι, loc ((c.attachCells j hj).π s) ⟶ k))

-- Only actual P-membership is supplied; no target model or desired source-Hom witness.
example : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) => P.homFamily)
    (((evaluation J C).obj k).map f) :=
  c.evaluateFreeDiagramsInProperty κ g loc k hLimit hSource hTarget hPushout P hg hSmall

example :
    (c.evaluateFreeDiagramsInProperty κ g loc k hLimit hSource hTarget hPushout
      P hg hSmall).F = c.F ⋙ (evaluation J C).obj k :=
  c.evaluateFreeDiagramsInProperty_F κ g loc k hLimit hSource hTarget hPushout P hg hSmall

example (j : κ.ord.ToType) :
    (c.evaluateFreeDiagramsInProperty κ g loc k hLimit hSource hTarget hPushout
      P hg hSmall).incl.app j = (c.incl.app j).app k :=
  c.evaluateFreeDiagramsInProperty_incl κ g loc k hLimit hSource hTarget hPushout
    P hg hSmall j

section SourceHom

variable [Fact κ.IsRegular]
  (hP : P.IsCardinalForSmallObjectArgument κ) {A₀ B₀ : C} (i : A₀ ⟶ B₀) (hi : P i)

example : PreservesColimit (c.F ⋙ (evaluation J C).obj k) (coyoneda.obj (op A₀)) :=
  c.preservesColimit_evaluatedFreeDiagrams κ g loc k hLimit hSource hTarget hPushout
    P hg hSmall hP i hi

example : PreservesColimit c.F
    (coyoneda.obj (op ((evaluationLeftAdjoint C k).obj A₀))) :=
  c.preservesColimit_freeDiagramSource κ g loc k hLimit hSource hTarget hPushout
    P hg hSmall hP i hi

end SourceHom

#check @RelativeCellComplex.evaluateFreeDiagramsInProperty
#check @RelativeCellComplex.evaluateFreeDiagramsInProperty_F
#check @RelativeCellComplex.evaluateFreeDiagramsInProperty_incl
#check @RelativeCellComplex.preservesColimit_evaluatedFreeDiagrams
#check @RelativeCellComplex.preservesColimit_freeDiagramSource
#print axioms RelativeCellComplex.evaluateFreeDiagramsInProperty
#print axioms RelativeCellComplex.evaluateFreeDiagramsInProperty_F
#print axioms RelativeCellComplex.evaluateFreeDiagramsInProperty_incl
#print axioms RelativeCellComplex.preservesColimit_evaluatedFreeDiagrams
#print axioms RelativeCellComplex.preservesColimit_freeDiagramSource

end DiagramSourceSmallnessTests
