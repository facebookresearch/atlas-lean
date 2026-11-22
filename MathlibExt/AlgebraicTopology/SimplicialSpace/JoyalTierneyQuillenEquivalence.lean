/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceCriterion
import MathlibExt.AlgebraicTopology.SimplicialSpace.JoyalTierneyQuillen
import MathlibExt.AlgebraicTopology.SimplicialSpace.GammaReplacement
import MathlibExt.AlgebraicTopology.SimplicialSpace.DerivedCounit

/-!
# The Joyal–Tierney Quillen equivalence

The original comparison adjunction is a Quillen equivalence for the actual
Joyal and Rezk models. The original Gamma comparison and its zeroth-row
isomorphism give weak reflection between fibrant Joyal objects. The original
counit gives the bifibrant-source criterion, and native replacement and
lifting extend it to every original cofibrant source.

This is Joyal–Tierney Theorem 4.11 in the native Hovey formulation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MorphismProperty

universe u

namespace SimplicialSpace

section

@[instance_reducible]
private def joyalModel : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
@[instance_reducible]
private def rezkModel : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory

attribute [local instance] joyalModel rezkModel

private abbrev comparisonGamma : JoyalSSet.{u} ⥤ SimplicialSpace.{u} :=
  (JoyalSSet.forget ⋙ SSet.Rezk.gammaDiagram) ⋙ ofSimplicialObject

private def comparisonEta : comparisonLeft.{u} ⟶ comparisonGamma.{u} :=
  ((Functor.whiskeringRight JoyalSSet.{u} (SimplicialObject SSet.{u})
    SimplicialSpace.{u}).obj ofSimplicialObject).map
      (((Functor.whiskeringLeft JoyalSSet.{u} SSet.{u}
        (SimplicialObject SSet.{u})).obj JoyalSSet.forget).map SSet.Rezk.gammaUnit)

private def comparisonGammaRowIso :
    comparisonGamma.{u} ⋙ comparisonRight.{u} ≅ 𝟭 JoyalSSet.{u} :=
  NatIso.ofComponents
    (fun Q => InducedCategory.isoMk (SSet.Rezk.gammaZerothRowIso.app Q.toSSet))
    (by
      intro Q Q' f
      apply InducedCategory.hom_ext
      exact SSet.Rezk.gammaZerothRowIso.hom.naturality (JoyalSSet.forget.map f))


private lemma comparisonLeft_reflects_between_fibrant
    {Q Q' : JoyalSSet.{u}} [IsFibrant Q] [IsFibrant Q'] (f : Q ⟶ Q')
    [WeakEquivalence (comparisonLeft.map f)] : WeakEquivalence f := by
  let : comparisonAdjunction.{u}.IsQuillenAdjunction := comparisonAdjunction_isQuillen
  let : SSet.Quasicategory Q.toSSet := (JoyalSSet.isFibrant_iff_quasicategory Q).mp inferInstance
  let : SSet.Quasicategory Q'.toSSet := (JoyalSSet.isFibrant_iff_quasicategory Q').mp inferInstance
  have hQ := SSet.Rezk.gammaDiagram_replacement Q.toSSet
  have hQ' := SSet.Rezk.gammaDiagram_replacement Q'.toSSet
  let : IsFibrant (comparisonGamma.obj Q) :=
    (RezkModel.isFibrant_iff_completeSegalSpaces _).mpr hQ.1
  let : IsFibrant (comparisonGamma.obj Q') :=
    (RezkModel.isFibrant_iff_completeSegalSpaces _).mpr hQ'.1
  let : WeakEquivalence (comparisonEta.app Q) := by
    rw [weakEquivalence_iff]
    change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences _
    rw [RezkModel.modelCategory_weakEquivalences]
    exact hQ.2.1
  let : WeakEquivalence (comparisonEta.app Q') := by
    rw [weakEquivalence_iff]
    change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences _
    rw [RezkModel.modelCategory_weakEquivalences]
    exact hQ'.2.1
  let : WeakEquivalence (comparisonEta.app Q ≫ comparisonGamma.map f) := by
    rw [← comparisonEta.naturality f]
    infer_instance
  let : WeakEquivalence (comparisonGamma.map f) :=
    weakEquivalence_of_precomp (comparisonEta.app Q) (comparisonGamma.map f)
  let : WeakEquivalence (comparisonRight.map (comparisonGamma.map f)) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := comparisonAdjunction) (comparisonGamma.map f)
  let : WeakEquivalence ((comparisonGammaRowIso.app Q).hom ≫ f) := by
    change WeakEquivalence (comparisonGammaRowIso.hom.app Q ≫ (𝟭 JoyalSSet).map f)
    rw [← comparisonGammaRowIso.hom.naturality f]
    change WeakEquivalence (comparisonRight.map (comparisonGamma.map f) ≫
      (comparisonGammaRowIso.app Q').hom)
    infer_instance
  exact weakEquivalence_of_precomp (comparisonGammaRowIso.app Q).hom f

end

/-- The original comparison adjunction is a Quillen equivalence for the
actual Joyal and Rezk models, with the full original-cofibrant-source Hovey field. -/
theorem comparisonAdjunction_isQuillenEquivalence :
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    comparisonAdjunction.{u}.IsQuillenEquivalence := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let : comparisonAdjunction.{u}.IsQuillenAdjunction := comparisonAdjunction_isQuillen
  apply Adjunction.IsQuillenEquivalence.mkOfFibrantSourceCriterion comparisonAdjunction
  intro Q X hQcof hQfib hXfib f
  let : IsFibrant (comparisonRight.obj X) :=
    (Adjunction.IsQuillenAdjunction.preservesFibrantObjects
      (adj := comparisonAdjunction)).isFibrant hXfib
  let : IsCofibrant (comparisonRight.obj X) := JoyalSSet.isCofibrant _
  have hXcss := (RezkModel.isFibrant_iff_completeSegalSpaces X).mp hXfib
  let : WeakEquivalence (comparisonAdjunction.counit.app X) := by
    rw [weakEquivalence_iff]
    change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences _
    rw [RezkModel.modelCategory_weakEquivalences]
    exact comparisonAdjunction_counit_rezkWeak X hXcss
  let g : Q ⟶ comparisonRight.obj X := comparisonAdjunction.homEquiv Q X f
  have hfac : comparisonLeft.map g ≫ comparisonAdjunction.counit.app X = f := by
    have he := comparisonAdjunction.homEquiv_counit (g := g)
    exact he.symm.trans (Equiv.symm_apply_apply _ _)
  simp only [← weakEquivalence_iff]
  constructor
  · intro hf
    let : WeakEquivalence f := hf
    let : WeakEquivalence (comparisonLeft.map g) := weakEquivalence_of_postcomp_of_fac hfac
    exact comparisonLeft_reflects_between_fibrant g
  · intro hg
    let : WeakEquivalence g := hg
    let : WeakEquivalence (comparisonLeft.map g) :=
      Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
        (adj := comparisonAdjunction) g
    rw [← hfac]
    infer_instance

end SimplicialSpace
