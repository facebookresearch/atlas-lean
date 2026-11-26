/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.SmallObject.DiagramRelativeCells
public import MathlibExt.CategoryTheory.Adjunction.SourceHomColimit
public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w a uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits Opposite

namespace HomotopicalAlgebra.RelativeCellComplex

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

include hLimit hSource hTarget hPushout hg hSmall

/-- Flatten the actual free cells and reindex only their base-family membership. -/
def evaluateFreeDiagramsInProperty :
    RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) => P.homFamily)
      (((evaluation J C).obj k).map f) := by
  let d := c.evaluateFreeDiagramsOfSmall g loc k hLimit hSource hTarget hPushout hSmall
  exact
    { toTransfiniteCompositionOfShape := d.toTransfiniteCompositionOfShape
      attachCells := fun j hj =>
        (d.attachCells j hj).reindexCellTypes P.homFamily
          (fun i => ⟨Arrow.mk (g i), hg i⟩) (fun _ => Iso.refl _) }

/-- Property-family reindexing leaves the original evaluated diagram unchanged. -/
theorem evaluateFreeDiagramsInProperty_F :
    (evaluateFreeDiagramsInProperty κ g loc c k hLimit hSource hTarget hPushout
      P hg hSmall).F = c.F ⋙ (evaluation J C).obj k := rfl

/-- Property-family reindexing keeps each actual evaluated endpoint inclusion. -/
theorem evaluateFreeDiagramsInProperty_incl (j : κ.ord.ToType) :
    (evaluateFreeDiagramsInProperty κ g loc c k hLimit hSource hTarget hPushout
      P hg hSmall).incl.app j = (c.incl.app j).app k := by
  change (c.incl.app j).app k ≫ 𝟙 _ = (c.incl.app j).app k
  exact Category.comp_id _

section SourceHom

variable [Fact κ.IsRegular]

/-- Apply the base generator's original cardinal witness to the same evaluated P-cell complex. -/
theorem preservesColimit_evaluatedFreeDiagrams
    (hP : P.IsCardinalForSmallObjectArgument κ)
    {A₀ B₀ : C} (i : A₀ ⟶ B₀) (hi : P i) :
    PreservesColimit (c.F ⋙ (evaluation J C).obj k) (coyoneda.obj (op A₀)) := by
  let d := evaluateFreeDiagramsInProperty κ g loc c k hLimit hSource hTarget hPushout
    P hg hSmall
  have hBase : PreservesColimit d.F (coyoneda.obj (op A₀)) :=
    hP.preservesColimit i hi (((evaluation J C).obj k).map f) d
  change PreservesColimit (c.F ⋙ (evaluation J C).obj k)
    (coyoneda.obj (op A₀)) at hBase
  exact hBase

/-- The actual free-diagram source inherits preservation at the same cardinal and Hom universes. -/
theorem preservesColimit_freeDiagramSource
    (hP : P.IsCardinalForSmallObjectArgument κ)
    {A₀ B₀ : C} (i : A₀ ⟶ B₀) (hi : P i) :
    PreservesColimit c.F
      (coyoneda.obj (op ((evaluationLeftAdjoint C k).obj A₀))) := by
  let _ : PreservesColimit (c.F ⋙ (evaluation J C).obj k) (coyoneda.obj (op A₀)) :=
    preservesColimit_evaluatedFreeDiagrams κ g loc c k hLimit hSource hTarget hPushout
      P hg hSmall hP i hi
  exact (evaluationAdjunctionRight C k).preservesColimit_leftAdjointSource A₀ c.F

end SourceHom

end HomotopicalAlgebra.RelativeCellComplex
