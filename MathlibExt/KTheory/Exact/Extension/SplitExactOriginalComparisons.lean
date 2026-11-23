/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.SplitExactAuxiliaryRealizationConull
public import MathlibExt.KTheory.Exact.Extension.LocalizedFiberLeftCommaWeakEquivalence
public import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberComparison
public import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberLoopEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.LeftCommaQuillenB

/-!
# Derived original comparisons for a split exact category

Splitness of the original admissible rows derives the actual auxiliary
terminal-map family. The existing all-span, Cartesian comma and original
completed-Core comparison theorems then apply to their unchanged maps.
The actual full-path return from the original zero homotopy fiber gives the
weak Q-loop composite on all components.

No auxiliary, span, comma or completed comparison weakness is an input. The actual original object
and morphism
universes, rows, denominators, chosen zero vertex and raw loop topology remain.
-/

public section

universe u v

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory Simplicial

namespace AlgebraicKTheory.SplitExactOriginalComparisons

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

private theorem originalBasesConull
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    ∀ X : C, TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v}))) := by
  intro X
  exact AuxiliaryExtension.splitExactAuxiliary_realization_conull hSplit X

/-- Every actual Q arrow has a weak original pullback at all denominators;
its auxiliary-base family is derived from splitness of the original rows. -/
theorem splitExactOriginalSpanPullback_weak
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    {A B : QuillenQ C} (phi : A ⟶ B) :
    SSet.realizationWeakEquivalences
      (nerveMap (LocalizedBaseChange.baseChangeFunctor (C := C) phi)) := by
  exact LocalizedBaseChange.baseChangeNerveMap_mem_of_originalBases_conull
    (C := C) (originalBasesConull hSplit) phi

/-- The original Cartesian lift comparison supplies all actual left-comma
transitions, without declaring the lift natural transformation an isomorphism. -/
theorem splitExactOriginalLeftCommaTransition_weak
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    {A B : QuillenQ C} (phi : A ⟶ B) :
    SSet.realizationWeakEquivalences
      (nerveMap (StructuredArrow.map
        (T := ExtensionCategory.localizedTarget (C := C)) phi)) := by
  exact LocalizedBaseChange.leftCommaTransitionNerveMap_mem_of_originalBases_conull
    (C := C) (originalBasesConull hSplit) phi

/-- The existing opposite/fiber-transport comparison is weak at every
original Q object, with the full original total and path coordinates. -/
theorem splitExactOriginalLeftCommaComparison_weak
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (d : QuillenQ C) :
    TopCat.weakHomotopyEquivalences
      (SSet.leftCommaHomotopyFiberComparison.{u, 0, max u v}
        (ExtensionCategory.localizedTarget (C := C)) d) := by
  have hTransitions : ∀ (A B : QuillenQ C) (phi : A ⟶ B),
      TopCat.weakHomotopyEquivalences
        (SSet.toTop.map (nerveMap (StructuredArrow.map
          (T := ExtensionCategory.localizedTarget (C := C)) phi))) := by
    intro A B phi
    exact splitExactOriginalLeftCommaTransition_weak hSplit phi
  exact SSet.leftCommaHomotopyFiberComparison_mem_weakHomotopyEquivalences.{u, 0, max u v}
    (ExtensionCategory.localizedTarget (C := C)) hTransitions d

/-- Splitness gives weakness of the existing completed-Core-to-original-fiber
map, preserving every pair, denominator and carried opposite path. -/
theorem splitExactCompletedCoreToOriginalHomotopyFiber_weak
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    TopCat.weakHomotopyEquivalences
      (OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C)) := by
  exact OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber_mem_of_originalBases_conull
    (C := C) (originalBasesConull hSplit)

/-- The literal canonical completed-Core comparison followed by the actual
full-path return is weak into the entire original raw Q-loop space. -/
theorem splitExactCompletedCoreToOriginalQLoops_weak
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    TopCat.weakHomotopyEquivalences
      (OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C) ≫
        OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops (C := C)) := by
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _
    (splitExactCompletedCoreToOriginalHomotopyFiber_weak hSplit)
    (OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops_mem (C := C))

end AlgebraicKTheory.SplitExactOriginalComparisons

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory Simplicial

universe uFiberwiseObj vFiberwiseHom

namespace AlgebraicKTheory.SplitExactOriginalComparisons

variable {C : Type uFiberwiseObj} [Category.{vFiberwiseHom} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- Splitness of every original exact row gives a homotopy equivalence
of the literal split inclusion on the original completed and fixed-target spaces.
Its forward is the original native up-nerve realization, on all components. -/
def splitExactOriginalSplitInclusionHomotopyEquiv
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) (X : C) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (nerve (SInverse (Core C) (Core C)) :
        SSet.{max uFiberwiseObj vFiberwiseHom}))
      (SSet.toTop.obj (nerve (FixedTargetExtension.localizedRows (C := C) X) :
        SSet.{max uFiberwiseObj vFiberwiseHom})) :=
  SSet.RealizationCWUpgrade.realizationHomotopyEquiv
    (nerveMapCommonHomUp.{uFiberwiseObj, max uFiberwiseObj vFiberwiseHom, 0}
      (FixedTargetExtension.SplitInclusion.splitLocalizedFunctor X))
    (FixedTargetExtension.IteratedAction.Collapse.splitInclusionNerveMap_mem_of_originalBase_conull
      (originalBasesConull hSplit X))

private theorem originalSplitInclusionHomotopyEquivForwardComputed
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) (X : C) :
    (splitExactOriginalSplitInclusionHomotopyEquiv hSplit X).toFun =
      (SSet.toTop.map
        (nerveMapCommonHomUp.{uFiberwiseObj, max uFiberwiseObj vFiberwiseHom, 0}
          (FixedTargetExtension.SplitInclusion.splitLocalizedFunctor X))).hom := by
  unfold splitExactOriginalSplitInclusionHomotopyEquiv
  exact SSet.RealizationCWUpgrade.realizationHomotopyEquiv_toFun _ _

/-- The entire forward map is the SAME original split inclusion realization;
the common nerve value universe does not replace either original category. -/
theorem splitExactOriginalSplitInclusionHomotopyEquiv_toFun
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) (X : C) :
    (splitExactOriginalSplitInclusionHomotopyEquiv hSplit X).toFun =
      (SSet.toTop.map
        (nerveMapCommonHomUp.{uFiberwiseObj, max uFiberwiseObj vFiberwiseHom, 0}
          (FixedTargetExtension.SplitInclusion.splitLocalizedFunctor X))).hom :=
  originalSplitInclusionHomotopyEquivForwardComputed hSplit X

/-- Every actual contravariant Cartesian Quillen transition has a homotopy
equivalence on its original localized fibers, with both whole inverse families.
Weakness is derived from original split rows, never supplied as a premise. -/
def splitExactOriginalSpanPullbackHomotopyEquiv
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    {A B : QuillenQ C} (phi : A ⟶ B) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (nerve (Functor.Fiber (LocalizedBaseChange.projection (C := C)) B) :
        SSet.{max uFiberwiseObj vFiberwiseHom}))
      (SSet.toTop.obj (nerve (Functor.Fiber (LocalizedBaseChange.projection (C := C)) A) :
        SSet.{max uFiberwiseObj vFiberwiseHom})) :=
  SSet.RealizationCWUpgrade.realizationHomotopyEquiv
    (nerveMap (LocalizedBaseChange.baseChangeFunctor (C := C) phi))
    (splitExactOriginalSpanPullback_weak hSplit phi)

private theorem originalSpanPullbackHomotopyEquivForwardComputed
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    {A B : QuillenQ C} (phi : A ⟶ B) :
    (splitExactOriginalSpanPullbackHomotopyEquiv hSplit phi).toFun =
      (SSet.toTop.map (nerveMap (LocalizedBaseChange.baseChangeFunctor (C := C) phi))).hom := by
  unfold splitExactOriginalSpanPullbackHomotopyEquiv
  exact SSet.RealizationCWUpgrade.realizationHomotopyEquiv_toFun _ _

/-- The whole forward field retains the actual chosen Cartesian pullback,
including its original arrow, fibers and every denominator. -/
theorem splitExactOriginalSpanPullbackHomotopyEquiv_toFun
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    {A B : QuillenQ C} (phi : A ⟶ B) :
    (splitExactOriginalSpanPullbackHomotopyEquiv hSplit phi).toFun =
      (SSet.toTop.map (nerveMap (LocalizedBaseChange.baseChangeFunctor (C := C) phi))).hom :=
  originalSpanPullbackHomotopyEquivForwardComputed hSplit phi

end AlgebraicKTheory.SplitExactOriginalComparisons

end
