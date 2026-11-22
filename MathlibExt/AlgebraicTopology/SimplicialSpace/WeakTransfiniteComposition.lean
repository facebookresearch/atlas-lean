/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerHomColimits
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Continuous transfinite closure of monic Rezk weak maps

The original composition witness is carried through an actual inverse-image
class by ofLE before map. Shared inner-Hom preservation covers the final
colimit and every genuine strict initial segment. Native opposite LLP lifting
then gives weakness against every original same-universe complete Segal test.
This is categorical support for Rezk's localization route, §§9 and 12 of
*A model for the homotopy theory of homotopy theory*. No localized model or
arbitrary inverse-limit stability is supplied as a premise.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open CategoryTheory.MorphismProperty
open scoped SimplicialSpace.Inner
namespace SimplicialSpace

private theorem monicWeak_shape
    (J : Type u) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    (monomorphisms SimplicialSpace.{u} ⊓
      rezkWeakEquivalences.{u}).IsStableUnderTransfiniteCompositionOfShape J := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  constructor
  intro X Y f hf
  rcases hf with ⟨h⟩
  have hToCof : monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u} ≤
      cofibrations SimplicialSpace.{u} := by
    intro A B i hi
    exact (HomotopicalAlgebra.cofibration_iff i).1
      ((ReedyModel.cofibration_iff i).2 hi.1)
  have hCofStable :
      (cofibrations SimplicialSpace.{u}).IsStableUnderTransfiniteCompositionOfShape J := by
    rw [← trivialFibrations_llp SimplicialSpace.{u}]
    infer_instance
  have hCof : cofibrations SimplicialSpace.{u} f :=
    hCofStable.le _ ⟨h.ofLE hToCof⟩
  refine ⟨(ReedyModel.cofibration_iff f).1
    ((HomotopicalAlgebra.cofibration_iff f).2 hCof), ?_⟩
  intro Z hZ
  let G := (innerHomFunctor.{u}.flip.obj Z).rightOp
  let P : MorphismProperty SSet.{u}ᵒᵖ := (cofibrations SSet.{u}).op.llp
  have hToP : monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u} ≤
      P.inverseImage G := by
    intro A B i hi
    have hiCof : cofibrations SimplicialSpace.{u} i := hToCof _ hi
    let g := (innerHomFunctor.{u}.map i.op).app Z
    have hgF : fibrations SSet.{u} g :=
      ReedyModel.inner_precomp_fibration i Z hiCof hZ.1
    have hgTF : trivialFibrations SSet.{u} g := ⟨hgF, hi.2 Z hZ⟩
    have hgRLP : (cofibrations SSet.{u}).rlp g := by
      rw [cofibrations_rlp SSet.{u}]
      exact hgTF
    change (cofibrations SSet.{u}).op.llp g.op
    intro K L p hp
    have hl : HasLiftingProperty p.unop g := hgRLP _ hp
    simpa only [Quiver.Hom.op_unop] using hl.op
  let _ : PreservesColimitsOfShape J G := innerHom_rightOp_preservesColimitsOfShape J Z
  let _ : PreservesWellOrderContinuousOfShape J G :=
    { preservesColimitsOfShape := fun j hj =>
        innerHom_rightOp_preservesColimitsOfShape (Set.Iio j) Z }
  let hP : P.TransfiniteCompositionOfShape J (G.map f) :=
    (h.ofLE hToP).map
  have hPStable : P.IsStableUnderTransfiniteCompositionOfShape J := by
    dsimp only [P]
    infer_instance
  have hPG : P (G.map f) := hPStable.le _ ⟨hP⟩
  have hOriginalRLP : (cofibrations SSet.{u}).rlp
      ((innerHomFunctor.{u}.map f.op).app Z) := by
    intro A B i hi
    have hOpp : HasLiftingProperty
        ((innerHomFunctor.{u}.map f.op).app Z).op i.op := hPG _ hi
    simpa only [Quiver.Hom.unop_op] using hOpp.unop
  have hOriginalTF : trivialFibrations SSet.{u}
      ((innerHomFunctor.{u}.map f.op).app Z) := by
    rw [← cofibrations_rlp SSet.{u}]
    exact hOriginalRLP
  exact hOriginalTF.2

/-- Original monic ALL-CSS Rezk weak maps are stable at every permitted continuous shape. -/
theorem monomorphisms_inf_rezkWeakEquivalences_isStableUnderTransfiniteComposition :
    MorphismProperty.IsStableUnderTransfiniteComposition.{u}
      (monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u}) where
  isStableUnderTransfiniteCompositionOfShape J := monicWeak_shape J

end SimplicialSpace
