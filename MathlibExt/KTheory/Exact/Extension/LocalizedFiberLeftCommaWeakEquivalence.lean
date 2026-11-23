/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.LocalizedFiberLeftComma
public import MathlibExt.KTheory.Exact.Extension.LocalizedBaseChangeWeakEquivalence
public import MathlibExt.CategoryTheory.FiberedCategory.FiberedCommaRealization

/-!
# Weak transitions of the original fibered left-comma diagram

Every original Q pullback is weak from the kernel/middle and zero-span proofs.
The actual strict-fiber inclusions are weak from their Cartesian adjunctions.
The chosen-lift natural transformation compares both complete nerve routes.
Homotopy invariance and cancellation then give weakness of the original
left-comma transition. The ring theorem derives the original base hypotheses.
-/

universe u v uRing vModule

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal

namespace AlgebraicKTheory.LocalizedBaseChange

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- Original auxiliary-base weakness derives every full left-comma Q transition. -/
theorem leftCommaTransitionNerveMap_mem_of_originalBases_conull
    (hBase : ∀ X : C, TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v})))) {R S : QuillenQ C} (f : R ⟶ S) :
    SSet.realizationWeakEquivalences
      (nerveMap (StructuredArrow.map (T := projection (C := C)) f)) := by
  let B := baseChangeFunctor f
  let jR := Functor.fiberToStructuredArrow (p := projection (C := C)) R
  let jS := Functor.fiberToStructuredArrow (p := projection (C := C)) S
  let T := StructuredArrow.map (T := projection (C := C)) f
  have hB : SSet.realizationWeakEquivalences (nerveMap B) :=
    baseChangeNerveMap_mem_of_originalBases_conull hBase f
  have hR : SSet.realizationWeakEquivalences (nerveMap jR) :=
    Functor.IsPreFibered.fiberToStructuredArrow_mem_realizationWeakEquivalences.{
      u, max u v} (p := projection (C := C)) R
  have hS : SSet.realizationWeakEquivalences (nerveMap jS) :=
    Functor.IsPreFibered.fiberToStructuredArrow_mem_realizationWeakEquivalences.{
      u, max u v} (p := projection (C := C)) S
  let A : SSet.{max u v} := nerve (Functor.Fiber (projection (C := C)) S)
  let L : SSet.{max u v} := nerve (StructuredArrow R (projection (C := C)))
  let l : A ⟶ L := nerveMap B ≫ nerveMap jR
  let r : A ⟶ L := nerveMap jS ≫ nerveMap T
  have hNatural : SSet.Homotopy l r := by
    change SSet.Homotopy (nerveMap B ≫ nerveMap jR) (nerveMap jS ≫ nerveMap T)
    rw [nerveMap_comp, nerveMap_comp]
    exact NatTrans.nerveHomotopy (baseChangeToStructuredArrow f)
  have hLeft : SSet.realizationWeakEquivalences l :=
    SSet.realizationWeakEquivalences.comp_mem _ _ hB hR
  let H := SSet.realizeHomotopy A L l r hNatural
  have hRight : SSet.realizationWeakEquivalences r := by
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map r)
    exact (TopCat.weakHomotopyEquivalences_iff_of_homotopy H).1 hLeft
  exact SSet.realizationWeakEquivalences.of_precomp
    (nerveMap jS) (nerveMap T) hS hRight

/-- For every associative unital ring, all original Q-span left-comma transitions are weak. -/
theorem projectiveLeftCommaTransitionNerveMap_mem_realizationWeakEquivalences
    {R : Type uRing} [Ring R]
    {A B : QuillenQ (FGProjectiveCat.{vModule} R)} (f : A ⟶ B) :
    SSet.realizationWeakEquivalences
      (nerveMap (StructuredArrow.map
        (T := projection (C := FGProjectiveCat.{vModule} R)) f)) := by
  have hBase : ∀ X : FGProjectiveCat.{vModule} R, TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core (FGProjectiveCat.{vModule} R))
          (FixedTargetExtension (FGProjectiveCat.{vModule} R) X)) :
            SSet.{max uRing (vModule + 1)}))) := by
    intro X
    exact AuxiliaryExtension.projectiveAuxiliary_realization_conull X
  exact leftCommaTransitionNerveMap_mem_of_originalBases_conull
    (C := FGProjectiveCat.{vModule} R) hBase f

end AlgebraicKTheory.LocalizedBaseChange

end
