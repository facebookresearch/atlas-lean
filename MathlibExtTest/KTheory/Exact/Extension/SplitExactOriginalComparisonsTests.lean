/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Extension.SplitExactOriginalComparisons

/-! Direct original-map scope clients for the split-exact comparisons. -/

universe u v

noncomputable section

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory Simplicial
open AlgebraicKTheory AlgebraicKTheory.SplitExactOriginalComparisons

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

#check @AlgebraicKTheory.SplitExactOriginalComparisons.splitExactOriginalSpanPullback_weak
#print axioms AlgebraicKTheory.SplitExactOriginalComparisons.splitExactOriginalSpanPullback_weak
#check @AlgebraicKTheory.SplitExactOriginalComparisons.splitExactOriginalLeftCommaTransition_weak
#print axioms AlgebraicKTheory.SplitExactOriginalComparisons.splitExactOriginalLeftCommaTransition_weak
#check @AlgebraicKTheory.SplitExactOriginalComparisons.splitExactOriginalLeftCommaComparison_weak
#print axioms AlgebraicKTheory.SplitExactOriginalComparisons.splitExactOriginalLeftCommaComparison_weak
#check @AlgebraicKTheory.SplitExactOriginalComparisons.splitExactCompletedCoreToOriginalHomotopyFiber_weak
#print axioms AlgebraicKTheory.SplitExactOriginalComparisons.splitExactCompletedCoreToOriginalHomotopyFiber_weak
#check @AlgebraicKTheory.SplitExactOriginalComparisons.splitExactCompletedCoreToOriginalQLoops_weak
#print axioms AlgebraicKTheory.SplitExactOriginalComparisons.splitExactCompletedCoreToOriginalQLoops_weak

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

-- Arbitrary original Q arrows, rather than only the unit or the two zero spans.
example
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    {A B : QuillenQ C} (phi : A ⟶ B) :
    SSet.realizationWeakEquivalences
      (nerveMap (LocalizedBaseChange.baseChangeFunctor (C := C) phi)) := by
  exact splitExactOriginalSpanPullback_weak hSplit phi

-- The full actual precomposition family in the original fibered comma model.
example
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    {A B : QuillenQ C} (phi : A ⟶ B) :
    SSet.realizationWeakEquivalences
      (nerveMap (StructuredArrow.map
        (T := ExtensionCategory.localizedTarget (C := C)) phi)) := by
  exact splitExactOriginalLeftCommaTransition_weak hSplit phi

-- Every chosen original base object, with the existing opposite comparison map.
example
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (d : QuillenQ C) :
    TopCat.weakHomotopyEquivalences
      (SSet.leftCommaHomotopyFiberComparison.{u, 0, max u v}
        (ExtensionCategory.localizedTarget (C := C)) d) := by
  exact splitExactOriginalLeftCommaComparison_weak hSplit d

-- The actual completed-Core comparison uses the whole original zero homotopy fiber.
example
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    TopCat.weakHomotopyEquivalences
      (OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C)) := by
  exact splitExactCompletedCoreToOriginalHomotopyFiber_weak hSplit

-- The existing full-path return gives the literal original weak Q-loop composite.
example
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    TopCat.weakHomotopyEquivalences
      (OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C) ≫
        OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops (C := C)) := by
  exact splitExactCompletedCoreToOriginalQLoops_weak hSplit

end
