/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveHomotopy
public import MathlibExt.KTheory.Exact.Extension.CompletedFiberCollapseWeakEquivalence
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Weakness of the original localized middle projection

The literal split inclusion followed by the middle projection is naturally
isomorphic to positive right translation by the given quotient. Realizing
this full natural homotopy gives weakness of the composite on every component.
The proved split-inclusion comparison then gives weakness of the original
middle projection. The projective case uses an associative unital ring,
retaining every original row, denominator and K0 component.
-/

universe u v uRing vModule

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open CategoryTheory.GenericCoreResidualTranslation CategoryTheory.GenericCoreTranslation
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

namespace AlgebraicKTheory.FixedTargetExtension.SplitInclusion

section General

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The actual up/down split-middle composite is weak by its full positive-translation homotopy. -/
theorem splitMiddleCompositeNerveMap_mem_realizationWeakEquivalences (X : C) :
    SSet.realizationWeakEquivalences
      (nerveMapCommonHomUp.{u, max u v, 0} (splitLocalizedFunctor X) ≫
        nerveMapCommonHom.{u, max u v, 0} (localizedMiddleFunctor X)) := by
  let K : SSet.{max u v} := nerve (SInverse (Core C) (Core C))
  let V : SSet.{max u v} := nerve (localizedRows (C := C) X)
  let eta : K ⟶ V := nerveMapCommonHomUp.{u, max u v, 0} (splitLocalizedFunctor X)
  let beta : V ⟶ K := nerveMapCommonHom.{u, max u v, 0} (localizedMiddleFunctor X)
  let q : K ⟶ K := nerveMap (splitLocalizedFunctor X ⋙ localizedMiddleFunctor X)
  let p : K ⟶ K := positiveNerveMap (⟨X⟩ : Core C)
  have hMap : eta ≫ beta = q :=
    nerveMapCommonHomUp_comp.{u, max u v, 0} (splitLocalizedFunctor X) (localizedMiddleFunctor X)
  have hSimplicial : SSet.Homotopy q p :=
    NatTrans.nerveHomotopy (splitLocalizedMiddleIso X).hom
  let H := SSet.realizeHomotopy K K q p hSimplicial
  have hP : SSet.realizationWeakEquivalences p := by
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map p)
    exact TopCat.homotopyEquiv_toFun_mem (positiveRealizedEquiv (⟨X⟩ : Core C))
  have hQ : SSet.realizationWeakEquivalences q := by
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map q)
    exact (TopCat.weakHomotopyEquivalences_iff_of_homotopy H).2 hP
  change SSet.realizationWeakEquivalences (eta ≫ beta)
  rw [hMap]
  exact hQ

/-- Terminal weakness of the original auxiliary base gives weakness of its whole middle map. -/
theorem localizedMiddleNerveMap_mem_of_originalBase_conull
    (hBase : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v})))) :
    SSet.realizationWeakEquivalences (nerveMapCommonHom.{u, max u v, 0} (localizedMiddleFunctor X))
      := by
  let K : SSet.{max u v} := nerve (SInverse (Core C) (Core C))
  let V : SSet.{max u v} := nerve (localizedRows (C := C) X)
  let eta : K ⟶ V := nerveMapCommonHomUp.{u, max u v, 0} (splitLocalizedFunctor X)
  let beta : V ⟶ K := nerveMapCommonHom.{u, max u v, 0} (localizedMiddleFunctor X)
  have hEta : SSet.realizationWeakEquivalences eta :=
    IteratedAction.Collapse.splitInclusionNerveMap_mem_of_originalBase_conull
      (C := C) (X := X) hBase
  have hComposite : SSet.realizationWeakEquivalences (eta ≫ beta) :=
    splitMiddleCompositeNerveMap_mem_realizationWeakEquivalences X
  exact SSet.realizationWeakEquivalences.of_precomp eta beta hEta hComposite

end General

section Projective

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- Every original projective quotient over an associative unital ring has a weak middle map. -/
theorem projectiveLocalizedMiddleNerveMap_mem_realizationWeakEquivalences
    {R : Type uRing} [Ring R] (X : FGProjectiveCat.{vModule} R) :
    SSet.realizationWeakEquivalences (nerveMapCommonHom.{max uRing (vModule + 1), max uRing
      (vModule + 1), 0} (localizedMiddleFunctor X)) := by
  have hBase := AlgebraicKTheory.AuxiliaryExtension.projectiveAuxiliary_realization_conull X
  exact localizedMiddleNerveMap_mem_of_originalBase_conull
    (C := FGProjectiveCat.{vModule} R) (X := X) hBase

end Projective

end AlgebraicKTheory.FixedTargetExtension.SplitInclusion

end
