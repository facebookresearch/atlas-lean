/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalizerDesignation
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalSmithModel
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkModelCategory
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-!
# Original simplex-index localizer and the existing designated Rezk model

The original spine and source-zero completeness family has precisely the
complete Segal spaces as its local targets. The all-arrow weak predicate and
the three model classes agree under the actual raw/designated carrier
equivalence. The original family is SSet.Rezk.localizingMap without relabelling.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Opposite
open scoped Simplicial SimplicialSpace.Inner
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.OriginalRezkLocalizer

private abbrev Raw := SimplicialPresheaf.{u} SimplexCategory

private abbrev designate : Raw.{u} ⥤ SimplicialSpace.{u} :=
  SimplicialSpace.ofSimplicialObject

private abbrev coefficientFamily := SSet.Rezk.localizingMap.{u}

private theorem coefficient_trivial_iff
    {A B : Raw.{u}} (f : A ⟶ B) :
    InjectiveKan.localTrivialMonomorphisms coefficientFamily.{u} f ↔
      (monomorphisms SimplicialSpace.{u} ⊓ SimplicialSpace.rezkWeakEquivalences)
        (designate.map f) :=
  and_congr (SimplicialSpace.mono_forget_map_iff (designate.map f))
    (coefficientLocalWeak_iff_rezkWeak f)

/-- Both EXISTING selected models agree in their three original classes under designation,
and their actual equivalence adjunction satisfies the full native Hovey criterion. -/
theorem coefficientModel_classes_and_equivalence :
    let MS := InjectiveKan.originalLocalSmithModel SSet.Rezk.localizingMap.{u}
    let MR := SimplicialSpace.RezkModel.modelCategory.{u}
    MS.categoryWithCofibrations.cofibrations =
        MR.categoryWithCofibrations.cofibrations.inverseImage SimplicialSpace.ofSimplicialObject ∧
      MS.categoryWithWeakEquivalences.weakEquivalences =
        MR.categoryWithWeakEquivalences.weakEquivalences.inverseImage
            SimplicialSpace.ofSimplicialObject ∧
      MS.categoryWithFibrations.fibrations =
        MR.categoryWithFibrations.fibrations.inverseImage SimplicialSpace.ofSimplicialObject ∧
      @CategoryTheory.Adjunction.IsQuillenEquivalence
        (SimplicialPresheaf.{u} SimplexCategory) inferInstance
        SimplicialSpace.{u} inferInstance MS MR
        SimplicialSpace.ofSimplicialObject SimplicialSpace.forget
        SimplicialSpace.equivalenceSimplicialObject.symm.toAdjunction := by
  let q := InjectiveKan.originalLocalSmithData SSet.Rezk.localizingMap.{u}
  let MS := q.model
  let MR := SimplicialSpace.RezkModel.modelCategory.{u}
  have hC : MS.categoryWithCofibrations.cofibrations =
      MR.categoryWithCofibrations.cofibrations.inverseImage designate := by
    rw [q.cofibrations_eq, SimplicialSpace.RezkModel.modelCategory_cofibrations]
    ext A B f
    exact SimplicialSpace.mono_forget_map_iff (designate.map f)
  have hW : MS.categoryWithWeakEquivalences.weakEquivalences =
      MR.categoryWithWeakEquivalences.weakEquivalences.inverseImage designate := by
    rw [q.weakEquivalences_eq, SimplicialSpace.RezkModel.modelCategory_weakEquivalences]
    ext A B f
    exact coefficientLocalWeak_iff_rezkWeak f
  have hF : MS.categoryWithFibrations.fibrations =
      MR.categoryWithFibrations.fibrations.inverseImage designate := by
    rw [q.fibrations_eq, SimplicialSpace.RezkModel.modelCategory_fibrations]
    let Q := monomorphisms SimplicialSpace.{u} ⊓ SimplicialSpace.rezkWeakEquivalences
    have hQ : Q.inverseImage designate =
        InjectiveKan.localTrivialMonomorphisms coefficientFamily.{u} := by
      ext A B f
      exact (coefficient_trivial_iff f).symm
    ext A B p
    change (InjectiveKan.localTrivialMonomorphisms coefficientFamily.{u}).rlp p ↔
      Q.rlp (designate.map p)
    rw [← hQ]
    have hRlp : (Q.inverseImage designate).rlp = Q.rlp.inverseImage designate :=
      (inverseImage_rlp_of_equivalence SimplicialSpace.equivalenceSimplicialObject.symm Q).symm
    exact Iff.of_eq (congrArg (fun P : MorphismProperty Raw.{u} => P p) hRlp)
  refine ⟨hC, hW, hF, ?_⟩
  refine @CategoryTheory.Adjunction.IsQuillenEquivalence.mk
    Raw.{u} inferInstance SimplicialSpace.{u} inferInstance MS MR
    designate SimplicialSpace.forget
        SimplicialSpace.equivalenceSimplicialObject.symm.toAdjunction ?_ ?_
  · refine @CategoryTheory.Adjunction.IsQuillenAdjunction.mk
      Raw.{u} inferInstance SimplicialSpace.{u} inferInstance MS MR
      designate SimplicialSpace.forget
          SimplicialSpace.equivalenceSimplicialObject.symm.toAdjunction ?_ ?_
    · intro A B f hf
      change MS.categoryWithCofibrations.cofibrations f at hf
      change MR.categoryWithCofibrations.cofibrations (designate.map f)
      rwa [hC] at hf
    · intro A B f hf
      change MS.categoryWithCofibrations.cofibrations f ∧
        MS.categoryWithWeakEquivalences.weakEquivalences f at hf
      change MR.categoryWithCofibrations.cofibrations (designate.map f) ∧
        MR.categoryWithWeakEquivalences.weakEquivalences (designate.map f)
      rwa [hC, hW] at hf
  · intro A Z _ _ f
    change MR.categoryWithWeakEquivalences.weakEquivalences f ↔
      MS.categoryWithWeakEquivalences.weakEquivalences
        ((SimplicialSpace.equivalenceSimplicialObject.symm.toAdjunction).homEquiv A Z f)
    rw [SimplicialSpace.RezkModel.modelCategory_weakEquivalences, q.weakEquivalences_eq]
    have hAdj : (SimplicialSpace.equivalenceSimplicialObject.symm.toAdjunction).homEquiv A Z
        f = f.hom := by
      rfl
    rw [hAdj]
    exact (coefficientLocalWeak_iff_rezkWeak f.hom).symm

end SimplicialPresheaf.OriginalRezkLocalizer
