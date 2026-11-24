/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.SmallObject.DiagramEvaluation

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w t a uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra.RelativeCellComplex

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

include hLimit hSource hTarget hPushout

/-- Evaluate the actual free-diagram complex and flatten each actual successor attachment. -/
def evaluateFreeDiagrams :
    RelativeCellComplex.{max w vJ} (fun (_ : T) => g) (((evaluation J C).obj k).map f) where
  __ := c.toTransfiniteCompositionOfShape.mapOfPreserves ((evaluation J C).obj k) hLimit
  attachCells j hj := by
    let _ := hSource j hj
    let _ := hTarget j hj
    let _ := hPushout j hj
    exact (c.attachCells j hj).evaluateFreeDiagrams g loc k

/-- The base complex uses the original evaluated diagram, with the caller's same ordinal bottom. -/
theorem evaluateFreeDiagrams_F :
    (evaluateFreeDiagrams g loc c k hLimit hSource hTarget hPushout).F =
      c.F ⋙ (evaluation J C).obj k := rfl

/-- The base complex retains the original evaluated endpoint cocone and its actual inclusions. -/
theorem evaluateFreeDiagrams_incl (j : T) :
    (evaluateFreeDiagrams g loc c k hLimit hSource hTarget hPushout).incl.app j =
      (c.incl.app j).app k := by
  change (c.incl.app j).app k ≫ 𝟙 _ = (c.incl.app j).app k
  exact Category.comp_id _

/-- Shrink only the actual successor cell labels, retaining the same evaluated complex. -/
def evaluateFreeDiagramsOfSmall
    (hSmall : ∀ (j : T) (hj : ¬ IsMax j),
      Small.{w} (Σ s : (c.attachCells j hj).ι, loc ((c.attachCells j hj).π s) ⟶ k)) :
    RelativeCellComplex.{w} (fun (_ : T) => g) (((evaluation J C).obj k).map f) where
  __ := c.toTransfiniteCompositionOfShape.mapOfPreserves ((evaluation J C).obj k) hLimit
  attachCells j hj := by
    let _ := hSource j hj
    let _ := hTarget j hj
    let _ := hPushout j hj
    let _ := hSmall j hj
    exact (c.attachCells j hj).evaluateFreeDiagramsOfSmall g loc k

end HomotopicalAlgebra.RelativeCellComplex
