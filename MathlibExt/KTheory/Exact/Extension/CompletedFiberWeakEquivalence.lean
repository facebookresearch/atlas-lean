/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.IteratedLocalizedRows
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBKFiberTransfer
public import MathlibExt.KTheory.Exact.Extension.ProjectiveAuxiliaryRealizationConull

/-!
# Weak equivalences for completed K fibers
-/

/-!
The literal completed K inclusion is weak in the original iterated total
category. The generic lemma takes only the original auxiliary-base conull
condition: its ordinary comma transitions and Psi comparison are already
derived from the actual action/lift maps. The all-ring application obtains
that base condition from the proved original auxiliary L theorem.

The proof uses the right-comma homotopy-fiber comparison and the conull
realization of the original auxiliary category. The projective application
holds for arbitrary associative unital rings and the whole completed category.
-/

universe u v uRing vModule

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

section General

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- Actual comma transitions, the derived Psi comparison and the original
base conull make the literal total-category J_E map weak. -/
theorem completedFiberNerveMap_mem_of_originalBase_conull
    (E : FixedTargetExtension C X)
    (hBase : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v})))) :
    SSet.realizationWeakEquivalences (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberFunctor
      E)) := by
  let p := iteratedRowProjectionFunctor (C := C) (X := X)
  let d : MonoidalActionCategory (Core C) (FixedTargetExtension C X) := ⟨E⟩
  have hTransition : ∀ (a b : MonoidalActionCategory (Core C) (FixedTargetExtension C X))
      (g : a ⟶ b), TopCat.weakHomotopyEquivalences
        (SSet.toTop.map ((SSet.rightCommaNerveDiagram p).map g)) := by
    intro a b g
    change TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (nerveMap (CostructuredArrow.map (S := p) g)))
    exact iteratedRowProjection_rightCommaTransition_mem_weakHomotopyEquivalences g
  have hProjection : SSet.realizationWeakEquivalences
      (nerveMap (CostructuredArrow.proj p d)) :=
    SSet.rightCommaProjection_mem_of_base_conull.{max u v, max u v, 0}
      p hTransition hBase d
  have hPsi : SSet.realizationWeakEquivalences
      (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberCommaFunctor E)) :=
    completedFiberCommaNerveMap_mem_realizationWeakEquivalences E
  have hComposite := SSet.realizationWeakEquivalences.comp_mem
    (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberCommaFunctor E))
    (nerveMap (CostructuredArrow.proj p d)) hPsi hProjection
  have hFunctor : completedFiberCommaFunctor E ⋙ CostructuredArrow.proj p d =
      completedFiberFunctor E := completedFiberCommaFunctor_projection E
  have hMap := nerveMapCommonHomUp_nerveMap_comp
    (completedFiberCommaFunctor E) (CostructuredArrow.proj p d)
  rw [hFunctor] at hMap
  exact hMap ▸ hComposite

end General

section Projective

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- For every associative unital ring, the original completed K map into N
is weak. Original L conull is derived, not a premise of this specialization. -/
theorem projectiveCompletedFiberNerveMap_mem_realizationWeakEquivalences
    {R : Type uRing} [Ring R] (X : FGProjectiveCat.{vModule} R)
    (E : FixedTargetExtension (FGProjectiveCat.{vModule} R) X) :
    SSet.realizationWeakEquivalences (nerveMapCommonHomUp.{max uRing (vModule + 1), max uRing
      (vModule + 1), 0} (completedFiberFunctor E)) := by
  exact completedFiberNerveMap_mem_of_originalBase_conull E
    (AlgebraicKTheory.AuxiliaryExtension.projectiveAuxiliary_realization_conull X)

end Projective

end AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

end
