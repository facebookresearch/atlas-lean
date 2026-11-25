/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.SmallObject.SelectiveMapping
import MathlibExt.CategoryTheory.SmallObject.FullyFaithful

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

noncomputable section

universe w a t vC vD uC uD

section Attachment

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {alpha : Type a} {A B : alpha → C} {g : ∀ i, A i ⟶ B i}
  {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f) (F : C ⥤ D)
  [PreservesColimit (Discrete.functor (fun i : c.ι => A (c.π i))) F]
  [PreservesColimit (Discrete.functor (fun i : c.ι => B (c.π i))) F]
  [PreservesColimit (span c.g₁ c.m) F]

example : AttachCells.{w} (fun i => F.map (g i)) (F.map f) := c.mapOfPreserves F
example : (c.mapOfPreserves F).ι = c.ι := rfl
example : (c.mapOfPreserves F).π = c.π := rfl
example : (c.mapOfPreserves F).cofan₁.pt = F.obj c.cofan₁.pt := rfl
example (i : c.ι) : (c.mapOfPreserves F).cofan₂.inj i = F.map (c.cofan₂.inj i) := rfl
example : (c.mapOfPreserves F).m = F.map c.m := rfl
example : (c.mapOfPreserves F).g₁ = F.map c.g₁ := rfl
example : (c.mapOfPreserves F).g₂ = F.map c.g₂ := rfl
example : IsPushout (F.map c.g₁) (F.map c.m) (F.map f) (F.map c.g₂) :=
  (c.mapOfPreserves F).isPushout

end Attachment

section ActualCocones

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {alpha : Type a} {A B : alpha → C} {g : ∀ i, A i ⟶ B i}
  {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f) (F : C ⥤ D)
  (hSource : IsColimit (F.mapCocone c.cofan₁))
  (hTarget : IsColimit (F.mapCocone c.cofan₂))
  [PreservesColimit (span c.g₁ c.m) F]

include hSource hTarget in
example : AttachCells.{w} (fun i => F.map (g i)) (F.map f) := by
  let _ := preservesColimit_of_preserves_colimit_cocone c.isColimit₁ hSource
  let _ := preservesColimit_of_preserves_colimit_cocone c.isColimit₂ hTarget
  exact c.mapOfPreserves F

end ActualCocones

section Transfinite

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
  {X Y : C} {f : X ⟶ Y} (c : TransfiniteCompositionOfShape T f) (F : C ⥤ D)
  [PreservesColimit c.F F]
  (hLimit : ∀ (k : T), Order.IsSuccLimit k →
    PreservesColimit ((Set.principalSegIio k).monotone.functor ⋙ c.F) F)

example : TransfiniteCompositionOfShape T (F.map f) := c.mapOfPreserves F hLimit
example : (c.mapOfPreserves F hLimit).F = c.F ⋙ F := rfl
example : (c.mapOfPreserves F hLimit).isoBot = F.mapIso c.isoBot := rfl
example : (c.mapOfPreserves F hLimit).incl =
    Functor.whiskerRight c.incl F ≫ (Functor.constComp _ _ _).hom := rfl
example : IsColimit (Cocone.mk (F.obj Y) (c.mapOfPreserves F hLimit).incl) :=
  (c.mapOfPreserves F hLimit).isColimit
example (k : T) (hk : Order.IsSuccLimit k) :
    IsColimit ((Set.principalSegIio k).cocone (c.F ⋙ F)) :=
  (c.mapOfPreserves F hLimit).F.isColimitOfIsWellOrderContinuous k hk

end Transfinite

section RelativeComplex

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
  {alpha : T → Type a} {A B : ∀ k, alpha k → C} {cell : ∀ k i, A k i ⟶ B k i}
  {X Y : C} {f : X ⟶ Y} (c : RelativeCellComplex.{w} cell f) (F : C ⥤ D)
  [PreservesColimit c.F F]
  (hLimit : ∀ (k : T), Order.IsSuccLimit k →
    PreservesColimit ((Set.principalSegIio k).monotone.functor ⋙ c.F) F)
  (hSource : ∀ (k : T) (hk : ¬ IsMax k), PreservesColimit
    (Discrete.functor (fun i : (c.attachCells k hk).ι => A k ((c.attachCells k hk).π i))) F)
  (hTarget : ∀ (k : T) (hk : ¬ IsMax k), PreservesColimit
    (Discrete.functor (fun i : (c.attachCells k hk).ι => B k ((c.attachCells k hk).π i))) F)
  (hPushout : ∀ (k : T) (hk : ¬ IsMax k), PreservesColimit
    (span (c.attachCells k hk).g₁ (c.attachCells k hk).m) F)

example : RelativeCellComplex.{w} (fun k i => F.map (cell k i)) (F.map f) :=
  c.mapOfPreserves F hLimit hSource hTarget hPushout
example : (c.mapOfPreserves F hLimit hSource hTarget hPushout).F = c.F ⋙ F := rfl
example (k : T) (hk : ¬ IsMax k) :
    ((c.mapOfPreserves F hLimit hSource hTarget hPushout).attachCells k hk).g₁ =
      F.map ((c.attachCells k hk).g₁) := rfl

end RelativeComplex

section AmbientProperty

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (F : C ⥤ D) (P : MorphismProperty C) (Q : MorphismProperty D)
  (hPQ : P ≤ Q.inverseImage F)
  {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun (_ : T) => P.homFamily) f)
  [PreservesColimit c.F F]
  (hLimit : ∀ (k : T), Order.IsSuccLimit k →
    PreservesColimit ((Set.principalSegIio k).monotone.functor ⋙ c.F) F)
  (hSource : ∀ (k : T) (hk : ¬ IsMax k), PreservesColimit
    (Discrete.functor (fun i : (c.attachCells k hk).ι => ((c.attachCells k hk).π i).1.left)) F)
  (hTarget : ∀ (k : T) (hk : ¬ IsMax k), PreservesColimit
    (Discrete.functor (fun i : (c.attachCells k hk).ι => ((c.attachCells k hk).π i).1.right)) F)
  (hPushout : ∀ (k : T) (hk : ¬ IsMax k), PreservesColimit
    (span (c.attachCells k hk).g₁ (c.attachCells k hk).m) F)

example : RelativeCellComplex.{w} (fun (_ : T) => Q.homFamily) (F.map f) :=
  c.mapOfLEOfPreserves F P Q hPQ hLimit hSource hTarget hPushout
example : (c.mapOfLEOfPreserves F P Q hPQ hLimit hSource hTarget hPushout).F = c.F ⋙ F := rfl

end AmbientProperty


section PublishedCompatibility

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {alpha : Type a} {A B : alpha → C} {g : ∀ i, A i ⟶ B i}
  {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f) (F : C ⥤ D)
  [PreservesColimitsOfSize.{w, w} F]

private theorem preservesSmallColimits : PreservesColimitsOfSize.{0, 0} F :=
  preservesSmallestColimits_of_preservesColimits F

attribute [local instance] preservesSmallColimits

example : (c.map F).m = (c.mapOfPreserves F).m := rfl

example : (c.map F).g₁ = (c.mapOfPreserves F).g₁ := rfl

end PublishedCompatibility

section SelectedFinalCocone

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
  {X Y : C} {f : X ⟶ Y} (c : TransfiniteCompositionOfShape T f) (F : C ⥤ D)
  (hFinal : IsColimit (F.mapCocone (Cocone.mk Y c.incl)))
  (hLimit : ∀ (k : T), Order.IsSuccLimit k →
    PreservesColimit ((Set.principalSegIio k).monotone.functor ⋙ c.F) F)

include hFinal hLimit in
example : TransfiniteCompositionOfShape T (F.map f) := by
  let _ := preservesColimit_of_preserves_colimit_cocone c.isColimit hFinal
  exact c.mapOfPreserves F hLimit

end SelectedFinalCocone

#print axioms HomotopicalAlgebra.AttachCells.mapOfPreserves
#print axioms CategoryTheory.TransfiniteCompositionOfShape.mapOfPreserves
#print axioms HomotopicalAlgebra.RelativeCellComplex.mapOfPreserves
#print axioms HomotopicalAlgebra.RelativeCellComplex.mapOfLEOfPreserves
